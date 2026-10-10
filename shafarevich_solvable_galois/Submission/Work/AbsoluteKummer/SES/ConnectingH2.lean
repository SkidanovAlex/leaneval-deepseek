import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.Connecting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.AbsoluteKummer.SES

open Work.AbsoluteKummer

/-- Induction principle for `H²` of the continuous cohomology: it suffices to check a predicate on
classes of continuous `2`-cocycles. -/
theorem H2_induction_on {G : Type*} [TopologicalSpace G] [Group G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] {C : Work.AbsoluteKummer.H2 G M → Prop}
    (x : Work.AbsoluteKummer.H2 G M)
    (h : ∀ c : Work.AbsoluteKummer.Z2 G M, C (Work.AbsoluteKummer.H2π G M c)) : C x := by
  obtain ⟨c, rfl⟩ :=
    QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  exact h c

end Work.AbsoluteKummer.SES

namespace Work.AbsoluteKummer.ShortExactSeq

open Work.AbsoluteKummer

open scoped Classical

noncomputable section

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]

/-! ## Lifting locally constant cochains along `π` -/

/-- A set-theoretic section of `π : N → P`. -/
noncomputable def sect (S : ShortExactSeq G M N P) (p : P) : N :=
  Classical.choose (S.pi_surjective p)

theorem pi_sect (S : ShortExactSeq G M N P) (p : P) : S.pi (S.sect p) = p :=
  Classical.choose_spec (S.pi_surjective p)

/-- The lift of a cochain `f : G → P` along `π`, obtained by composing with a section. -/
noncomputable def liftCochainC (S : ShortExactSeq G M N P) (f : G → P) : G → N :=
  fun g => S.sect (f g)

@[simp] theorem liftCochainC_apply (S : ShortExactSeq G M N P) (f : G → P) (g : G) :
    S.liftCochainC f g = S.sect (f g) := rfl

theorem pi_liftCochainC (S : ShortExactSeq G M N P) (f : G → P) (g : G) :
    S.pi (S.liftCochainC f g) = f g :=
  S.pi_sect (f g)

/-- The lift of a locally constant cochain is locally constant. -/
theorem isLocallyConstant_liftCochainC (S : ShortExactSeq G M N P) {f : G → P}
    (hf : IsLocallyConstant f) : IsLocallyConstant (S.liftCochainC f) :=
  IsLocallyConstant.map S.sect hf

/-- The differential of a lift of a `1`-cocycle lies in `ker π = range ι`. -/
theorem pi_d1_liftCochainC (S : ShortExactSeq G M N P) (c : Z1 G P) (g h : G) :
    S.pi (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h)) = 0 := by
  have h1 : S.pi (g • S.liftCochainC (c : G → P) h) = g • (c : G → P) h := by
    rw [S.pi_equivariant g, S.pi_liftCochainC]
  have h2 : S.pi (S.liftCochainC (c : G → P) (g * h)) = (c : G → P) (g * h) :=
    S.pi_liftCochainC _ _
  have h3 : S.pi (S.liftCochainC (c : G → P) g) = (c : G → P) g :=
    S.pi_liftCochainC _ _
  have hc : (c : G → P) (g * h) = g • (c : G → P) h + (c : G → P) g :=
    isCrossedHom_of_mem_Z1 c.2 g h
  simp only [Work.GroupCohomology.d1_apply, map_sub, map_add, h1, h2, h3, hc]
  abel

/-! ## The connecting cocycle -/

/-- The connecting map on cocycles: `Z¹(G,P) → Z²(G,M)`, defined by lifting a `1`-cocycle along
`π` and pulling `d¹` of the lift back along `ι`. -/
noncomputable def deltaCocycleC (S : ShortExactSeq G M N P) (c : Z1 G P) : Z2 G M :=
  ⟨fun p => S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) p), by
    rw [mem_Z2_iff]
    refine ⟨?_, IsLocallyConstant.map S.iotaInv
      (isLocallyConstant_d1 S.isDiscreteN
        (isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 c.2)))⟩
    intro g h k
    apply S.iota_injective
    have hI : ∀ p : G × G, S.iota
        (S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) p)) =
        Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) p := by
      rintro ⟨a, b⟩
      exact S.iota_iotaInv (S.mem_range_of_mem_ker (by
        rw [AddMonoidHom.mem_ker]
        exact S.pi_d1_liftCochainC c a b))
    have hZ : Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) ∈
        Work.GroupCohomology.Z2 G N :=
      Work.GroupCohomology.d1_mem_Z2 G N (S.liftCochainC (c : G → P))
    have hZc := (Work.GroupCohomology.mem_Z2_iff (G := G) (A := N)
      (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)))).mp hZ g h k
    calc S.iota (S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g * h, k)) +
            S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h)))
        = Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g * h, k) +
            Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h) := by
          rw [map_add, hI (g * h, k), hI (g, h)]
      _ = g • Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (h, k) +
            Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h * k) := hZc
      _ = S.iota (g • S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (h, k)) +
            S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h * k))) := by
          rw [map_add, S.iota_equivariant, hI (h, k), hI (g, h * k)]⟩

@[simp] theorem deltaCocycleC_apply (S : ShortExactSeq G M N P) (c : Z1 G P) (g h : G) :
    (S.deltaCocycleC c : G × G → M) (g, h) =
      S.iotaInv (Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h)) := rfl

theorem iota_deltaCocycleC (S : ShortExactSeq G M N P) (c : Z1 G P) (g h : G) :
    S.iota ((S.deltaCocycleC c : G × G → M) (g, h)) =
      Work.GroupCohomology.d1 G N (S.liftCochainC (c : G → P)) (g, h) :=
  S.iota_iotaInv (S.mem_range_of_mem_ker (by
    rw [AddMonoidHom.mem_ker]
    exact S.pi_d1_liftCochainC c g h))


/-! ## Additivity of the connecting cocycle -/

/-- The connecting cocycle is additive in the class: the difference of the chosen lifts of
`c + c'`, `c` and `c'` takes values in `ker π = range ι`, and pulling it back along `ι` exhibits
the difference `δ(c+c') - (δc + δc')` as a coboundary, hence as `0` in `H²`. -/
theorem deltaCocycleC_add (S : ShortExactSeq G M N P) (c c' : Z1 G P) :
    H2π G M (S.deltaCocycleC (c + c')) =
      H2π G M (S.deltaCocycleC c) + H2π G M (S.deltaCocycleC c') := by
  rw [← AddMonoidHom.map_add, H2π_eq_iff]
  set b'' : G → N := S.liftCochainC ((c + c' : Z1 G P) : G → P) with hb''
  set b : G → N := S.liftCochainC (c : G → P) with hb
  set b' : G → N := S.liftCochainC (c' : G → P) with hb'
  have hb''l : IsLocallyConstant b'' := by
    rw [hb'']; exact isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 (c + c').2)
  have hbl : IsLocallyConstant b := by
    rw [hb]; exact isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 c.2)
  have hb'l : IsLocallyConstant b' := by
    rw [hb']; exact isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 c'.2)
  have hker : ∀ g : G, b'' g - b g - b' g ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, hb'', hb, hb', map_sub, map_sub, S.pi_liftCochainC,
      S.pi_liftCochainC, S.pi_liftCochainC, AddSubgroup.coe_add, Pi.add_apply]
    abel
  set w : G → M := fun g => S.iotaInv (b'' g - b g - b' g) with hw
  have hwi : ∀ g : G, S.iota (w g) = b'' g - b g - b' g := by
    intro g
    rw [hw]
    exact S.iota_iotaInv (S.mem_range_of_mem_ker (hker g))
  have hwl : IsLocallyConstant w := by
    rw [hw]
    exact IsLocallyConstant.map S.iotaInv ((hb''l.sub hbl).sub hb'l)
  refine (mem_B2_iff _).mpr ⟨w, hwl, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  apply S.iota_injective
  have hL : S.iota (Work.GroupCohomology.d1 G M w (g, h)) =
      Work.GroupCohomology.d1 G N b'' (g, h) -
        (Work.GroupCohomology.d1 G N b (g, h) + Work.GroupCohomology.d1 G N b' (g, h)) := by
    rw [Work.GroupCohomology.d1_apply, map_add, map_sub, S.iota_equivariant]
    simp only [hwi, smul_sub, Work.GroupCohomology.d1_apply]
    abel
  have hR : S.iota (((S.deltaCocycleC (c + c') - (S.deltaCocycleC c + S.deltaCocycleC c') :
        Z2 G M) : G × G → M) (g, h)) =
      Work.GroupCohomology.d1 G N b'' (g, h) -
        (Work.GroupCohomology.d1 G N b (g, h) + Work.GroupCohomology.d1 G N b' (g, h)) := by
    have hce : ((S.deltaCocycleC (c + c') - (S.deltaCocycleC c + S.deltaCocycleC c') :
          Z2 G M) : G × G → M) (g, h) =
        (S.deltaCocycleC (c + c') : G × G → M) (g, h) -
          ((S.deltaCocycleC c : G × G → M) (g, h) +
            (S.deltaCocycleC c' : G × G → M) (g, h)) := by
      simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.sub_apply, Pi.add_apply]
    rw [hce, map_sub, map_add, S.iota_deltaCocycleC (c + c') g h,
      S.iota_deltaCocycleC c g h, S.iota_deltaCocycleC c' g h, hb'', hb, hb']
  exact hL.trans hR.symm

/-- The connecting cocycle of the zero cocycle is a coboundary. -/
theorem deltaCocycleC_zero (S : ShortExactSeq G M N P) :
    H2π G M (S.deltaCocycleC 0) = 0 := by
  have h : H2π G M (S.deltaCocycleC 0) =
      H2π G M (S.deltaCocycleC 0) + H2π G M (S.deltaCocycleC 0) := by
    simpa using deltaCocycleC_add S (0 : Z1 G P) 0
  have h2 : H2π G M (S.deltaCocycleC 0) + 0 =
      H2π G M (S.deltaCocycleC 0) + H2π G M (S.deltaCocycleC 0) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- The connecting map on cocycles, as an additive homomorphism `Z¹(G,P) →+ H²(G,M)`. -/
noncomputable def deltaZC (S : ShortExactSeq G M N P) : Z1 G P →+ H2 G M where
  toFun c := H2π G M (S.deltaCocycleC c)
  map_zero' := S.deltaCocycleC_zero
  map_add' := S.deltaCocycleC_add

@[simp] theorem deltaZC_apply (S : ShortExactSeq G M N P) (c : Z1 G P) :
    S.deltaZC c = H2π G M (S.deltaCocycleC c) := rfl

/-! ## Independence of the class of the connecting cocycle from the representative -/

/-- The connecting cocycle is constant on cohomology classes: if `H1π c = H1π c'`, then the
cocycles `δc` and `δc'` differ by a coboundary. -/
theorem deltaCocycleC_eq_class (S : ShortExactSeq G M N P) (c c' : Z1 G P)
    (h : H1π G P c = H1π G P c') :
    H2π G M (S.deltaCocycleC c) = H2π G M (S.deltaCocycleC c') := by
  rw [H2π_eq_iff]
  have hmem : ((c - c' : Z1 G P) : G → P) ∈ B1 G P := (H1π_eq_iff c c').mp h
  obtain ⟨a, ha⟩ := (mem_B1_iff _).mp hmem
  have ha' : ∀ g : G, g • a - a = (c : G → P) g - (c' : G → P) g := by
    intro g
    have hg := congrFun ha g
    simpa using hg
  set b₀ : N := S.sect a with hb₀def
  have hb₀π : S.pi b₀ = a := by rw [hb₀def]; exact S.pi_sect a
  set b : G → N := S.liftCochainC (c : G → P) with hb
  set b' : G → N := S.liftCochainC (c' : G → P) with hb'
  have hbl : IsLocallyConstant b := by
    rw [hb]; exact isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 c.2)
  have hb'l : IsLocallyConstant b' := by
    rw [hb']; exact isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 c'.2)
  have hd0l : IsLocallyConstant (Work.GroupCohomology.d0 G N b₀) :=
    isLocallyConstant_d0 S.isDiscreteN b₀
  have hmker : ∀ g : G, b g - b' g - (g • b₀ - b₀) ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, hb, hb', map_sub, map_sub, map_sub, S.pi_equivariant,
      S.pi_liftCochainC, S.pi_liftCochainC, hb₀π, ← ha' g]
    abel
  set m : G → N := fun g => b g - b' g - (g • b₀ - b₀) with hm
  have hmlc : IsLocallyConstant m := by
    rw [hm]; exact (hbl.sub hb'l).sub hd0l
  set k : G → M := fun g => S.iotaInv (m g) with hkdef
  have hk : ∀ g : G, S.iota (k g) = m g := by
    intro g
    rw [hkdef]
    exact S.iota_iotaInv (S.mem_range_of_mem_ker (hmker g))
  have hklc : IsLocallyConstant k := by
    rw [hkdef]; exact IsLocallyConstant.map S.iotaInv hmlc
  have hd1 : ∀ g h : G, Work.GroupCohomology.d1 G M k (g, h) =
      (S.deltaCocycleC c : G × G → M) (g, h) - (S.deltaCocycleC c' : G × G → M) (g, h) := by
    intro g h
    apply S.iota_injective
    have step1 : S.iota (Work.GroupCohomology.d1 G M k (g, h)) =
        Work.GroupCohomology.d1 G N m (g, h) := by
      have hmap := congrFun (Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant k)
        (g, h)
      rw [Work.GroupCohomology.mapCochain2_apply] at hmap
      rw [hmap, show Work.GroupCohomology.mapCochain1 G S.iota k = m from funext hk]
    have hm_eq : m = b - b' - Work.GroupCohomology.d0 G N b₀ := by
      funext g'
      rw [hm]
      simp only [Pi.sub_apply, Work.GroupCohomology.d0_apply]
    have step2 : Work.GroupCohomology.d1 G N m (g, h) =
        Work.GroupCohomology.d1 G N b (g, h) - Work.GroupCohomology.d1 G N b' (g, h) := by
      rw [hm_eq, map_sub, map_sub, Work.GroupCohomology.d1_d0, sub_zero, Pi.sub_apply]
    have step3 : Work.GroupCohomology.d1 G N b (g, h) - Work.GroupCohomology.d1 G N b' (g, h) =
        S.iota ((S.deltaCocycleC c : G × G → M) (g, h)) -
          S.iota ((S.deltaCocycleC c' : G × G → M) (g, h)) := by
      rw [hb, hb', ← S.iota_deltaCocycleC c g h, ← S.iota_deltaCocycleC c' g h]
    calc S.iota (Work.GroupCohomology.d1 G M k (g, h))
        = Work.GroupCohomology.d1 G N m (g, h) := step1
      _ = Work.GroupCohomology.d1 G N b (g, h) - Work.GroupCohomology.d1 G N b' (g, h) := step2
      _ = S.iota ((S.deltaCocycleC c : G × G → M) (g, h)) -
            S.iota ((S.deltaCocycleC c' : G × G → M) (g, h)) := step3
      _ = S.iota ((S.deltaCocycleC c : G × G → M) (g, h) -
            (S.deltaCocycleC c' : G × G → M) (g, h)) := by rw [map_sub]
  refine (mem_B2_iff _).mpr ⟨k, hklc, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  rw [hd1 g h, AddSubgroup.coe_sub, Pi.sub_apply]

/-! ## The connecting homomorphism `H¹(G,P) → H²(G,M)` -/

/-- **The connecting map** `δ¹ : H¹(G,P) →+ H²(G,M)` of a short exact sequence of discrete
`G`-modules. -/
noncomputable def deltaH2 (S : ShortExactSeq G M N P) : H1 G P →+ H2 G M :=
  QuotientAddGroup.lift ((B1 G P).comap (Z1 G P).subtype) S.deltaZC (by
    intro z hz
    have hz' : ((z : Z1 G P) : G → P) ∈ B1 G P := by
      simpa using (AddSubgroup.mem_comap.mp hz)
    have hker : H1π G P z = 0 := by
      rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hz'
    have h0 : H1π G P (0 : Z1 G P) = 0 := map_zero _
    have h := S.deltaCocycleC_eq_class z 0 (by rw [hker, h0])
    show S.deltaZC z = 0
    rw [show S.deltaZC z = H2π G M (S.deltaCocycleC z) from rfl, h]
    exact map_zero S.deltaZC)

theorem deltaH2_H1π (S : ShortExactSeq G M N P) (c : Z1 G P) :
    S.deltaH2 (H1π G P c) = H2π G M (S.deltaCocycleC c) :=
  QuotientAddGroup.lift_mk' _ _ c

end

end Work.AbsoluteKummer.ShortExactSeq
