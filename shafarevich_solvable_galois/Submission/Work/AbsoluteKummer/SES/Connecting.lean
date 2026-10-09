/-
Copyright (c) 2025. All rights reserved.

# The connecting map `H⁰(G,P) → H¹(G,M)` of a short exact sequence of discrete modules

For a short exact sequence `0 → M --ι--> N --π--> P → 0` of discrete `G`-modules, this file
constructs the connecting homomorphism of the long exact sequence in continuous cohomology

`H⁰(G,P) --δ--> H¹(G,M)`,

together with the two elementary exactness statements

* `S.range_mapH0_le_ker_delta` : `range (H⁰(π)) ≤ ker δ`,
* `S.range_delta_le_ker_mapH1` : `range δ ≤ ker (H¹(ι))`.

The construction: the function `ι⁻¹` inverting `ι` on `ker π = range ι`; for `p ∈ P^G` and a lift
`n ∈ N` of `p`, the cocycle `g ↦ ι⁻¹(g • n - n)`; the class of this cocycle in `H¹(G,M)` is
independent of the lift and additive in `p`.
-/
import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.AbsoluteKummer.ShortExactSeq

open Work.AbsoluteKummer

open scoped Classical

noncomputable section

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]

/-! ## The inverse of `ι` on `range ι = ker π` -/

/-- `ι⁻¹` on `range ι`, and `0` off it. -/
noncomputable def iotaInv (S : ShortExactSeq G M N P) (b : N) : M :=
  if h : b ∈ S.iota.range then Classical.choose (AddMonoidHom.mem_range.mp h) else 0

theorem iota_iotaInv (S : ShortExactSeq G M N P) {b : N} (hb : b ∈ S.iota.range) :
    S.iota (S.iotaInv b) = b := by
  unfold iotaInv
  rw [dif_pos hb]
  exact Classical.choose_spec (AddMonoidHom.mem_range.mp hb)

theorem mem_range_of_mem_ker (S : ShortExactSeq G M N P) {b : N} (hb : b ∈ S.pi.ker) :
    b ∈ S.iota.range := by
  rw [S.range_iota_eq_ker_pi]
  exact hb

theorem iotaInv_iota (S : ShortExactSeq G M N P) (a : M) : S.iotaInv (S.iota a) = a := by
  apply S.iota_injective
  rw [S.iota_iotaInv (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)]

theorem iotaInv_zero (S : ShortExactSeq G M N P) : S.iotaInv 0 = 0 := by
  apply S.iota_injective
  rw [S.iota_iotaInv (S.mem_range_of_mem_ker (S.pi.ker.zero_mem)), map_zero]

theorem iotaInv_add (S : ShortExactSeq G M N P) {b b' : N} (hb : b ∈ S.pi.ker)
    (hb' : b' ∈ S.pi.ker) : S.iotaInv (b + b') = S.iotaInv b + S.iotaInv b' := by
  apply S.iota_injective
  rw [map_add, S.iota_iotaInv (S.mem_range_of_mem_ker hb),
    S.iota_iotaInv (S.mem_range_of_mem_ker hb'),
    S.iota_iotaInv (S.mem_range_of_mem_ker (S.pi.ker.add_mem hb hb'))]

/-! ## The cocycle `g ↦ ι⁻¹(g • n - n)` attached to a lift `n` of an invariant element -/

theorem isLocallyConstant_smul_sub (S : ShortExactSeq G M N P) (n : N) :
    Work.AbsoluteKummer.IsLocallyConstant (fun g : G => g • n - n) :=
  Work.AbsoluteKummer.isLocallyConstant_d0 S.isDiscreteN n

theorem mem_ker_smul_sub (S : ShortExactSeq G M N P) (n : N) (hn : (S.pi n) ∈ H0 G P) (g : G) :
    g • n - n ∈ S.pi.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, S.pi_equivariant g n, hn g, sub_self]

theorem isCrossedHom_iotaInv (S : ShortExactSeq G M N P) (n : N) (hn : (S.pi n) ∈ H0 G P) :
    Work.GroupCohomology.IsCrossedHom G M (fun g : G => S.iotaInv (g • n - n)) := by
  intro g h
  apply S.iota_injective
  rw [map_add, S.iota_equivariant g (S.iotaInv (h • n - n)),
    S.iota_iotaInv (S.mem_range_of_mem_ker (S.mem_ker_smul_sub n hn (g * h))),
    S.iota_iotaInv (S.mem_range_of_mem_ker (S.mem_ker_smul_sub n hn h)),
    S.iota_iotaInv (S.mem_range_of_mem_ker (S.mem_ker_smul_sub n hn g)),
    mul_smul, smul_sub]
  abel

theorem isLocallyConstant_iotaInv_smul_sub (S : ShortExactSeq G M N P) (n : N) :
    Work.AbsoluteKummer.IsLocallyConstant (fun g : G => S.iotaInv (g • n - n)) := by
  intro g₀
  obtain ⟨U, hU, hgU, hc⟩ := S.isLocallyConstant_smul_sub n g₀
  exact ⟨U, hU, hgU, fun g hg => congrArg S.iotaInv (hc g hg)⟩

/-- The `1`-cocycle `g ↦ ι⁻¹(g • n - n)` attached to a lift `n` of an invariant element of `P`. -/
noncomputable def cocycleOf (S : ShortExactSeq G M N P) (n : N) (hn : (S.pi n) ∈ H0 G P) :
    Z1 G M :=
  ⟨fun g : G => S.iotaInv (g • n - n),
    Work.AbsoluteKummer.mem_Z1_of (f := fun g : G => S.iotaInv (g • n - n))
      (S.isCrossedHom_iotaInv n hn) (S.isLocallyConstant_iotaInv_smul_sub n)⟩

@[simp] theorem cocycleOf_apply (S : ShortExactSeq G M N P) (n : N) (hn : (S.pi n) ∈ H0 G P)
    (g : G) : (S.cocycleOf n hn : G → M) g = S.iotaInv (g • n - n) := rfl

theorem iota_cocycleOf (S : ShortExactSeq G M N P) (n : N) (hn : (S.pi n) ∈ H0 G P) (g : G) :
    S.iota ((S.cocycleOf n hn : G → M) g) = g • n - n := by
  rw [S.cocycleOf_apply]
  exact S.iota_iotaInv (S.mem_range_of_mem_ker (S.mem_ker_smul_sub n hn g))

theorem mem_H0_pi_add (S : ShortExactSeq G M N P) {n n' : N} (hn : (S.pi n) ∈ H0 G P)
    (hn' : (S.pi n') ∈ H0 G P) : (S.pi (n + n')) ∈ H0 G P := by
  rw [map_add]
  intro g
  rw [smul_add, hn g, hn' g]

theorem cocycleOf_add (S : ShortExactSeq G M N P) {n n' : N} (hn : (S.pi n) ∈ H0 G P)
    (hn' : (S.pi n') ∈ H0 G P) :
    S.cocycleOf (n + n') (S.mem_H0_pi_add hn hn') = S.cocycleOf n hn + S.cocycleOf n' hn' := by
  apply Subtype.ext
  funext g
  show S.iotaInv (g • (n + n') - (n + n')) =
      S.iotaInv (g • n - n) + S.iotaInv (g • n' - n')
  rw [show g • (n + n') - (n + n') = (g • n - n) + (g • n' - n') by rw [smul_add]; abel]
  exact S.iotaInv_add (S.mem_ker_smul_sub n hn g) (S.mem_ker_smul_sub n' hn' g)

/-! ## Independence of the class of the cocycle from the lift -/

theorem cocycleOf_sub_mem_B1 (S : ShortExactSeq G M N P) {n n' : N} (hn : (S.pi n) ∈ H0 G P)
    (hn' : (S.pi n') ∈ H0 G P) (h : S.pi n = S.pi n') :
    ((S.cocycleOf n hn - S.cocycleOf n' hn' : Z1 G M) : G → M) ∈ B1 G M := by
  have hmem : n - n' ∈ S.pi.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, h, sub_self]
  refine (Work.AbsoluteKummer.mem_B1_iff _).mpr ⟨S.iotaInv (n - n'), ?_⟩
  show Work.GroupCohomology.d0 G M (S.iotaInv (n - n')) =
    ((S.cocycleOf n hn - S.cocycleOf n' hn' : Z1 G M) : G → M)
  funext g
  apply S.iota_injective
  rw [Work.GroupCohomology.d0_apply, map_sub, S.iota_equivariant g (S.iotaInv (n - n')),
    S.iota_iotaInv (S.mem_range_of_mem_ker hmem), AddSubgroup.coe_sub, Pi.sub_apply, map_sub,
    S.iota_cocycleOf, S.iota_cocycleOf, smul_sub]
  abel

theorem class_eq (S : ShortExactSeq G M N P) {n n' : N} (hn : (S.pi n) ∈ H0 G P)
    (hn' : (S.pi n') ∈ H0 G P) (h : S.pi n = S.pi n') :
    H1π G M (S.cocycleOf n hn) = H1π G M (S.cocycleOf n' hn') := by
  rw [H1π_eq_iff]
  exact S.cocycleOf_sub_mem_B1 hn hn' h

theorem cocycleOf_eq_zero (S : ShortExactSeq G M N P) {n : N} (hn : (S.pi n) ∈ H0 G P)
    (hn0 : n ∈ H0 G N) : S.cocycleOf n hn = 0 := by
  apply Subtype.ext
  funext g
  apply S.iota_injective
  rw [S.iota_cocycleOf, hn0 g, sub_self]
  simp

theorem mem_B1_cocycleOf_of_pi_eq_zero (S : ShortExactSeq G M N P) {n : N}
    (hn : (S.pi n) ∈ H0 G P) (h0 : S.pi n = 0) : (S.cocycleOf n hn : G → M) ∈ B1 G M := by
  refine (Work.AbsoluteKummer.mem_B1_iff _).mpr ⟨S.iotaInv n, ?_⟩
  funext g
  apply S.iota_injective
  rw [Work.GroupCohomology.d0_apply, map_sub, S.iota_equivariant g (S.iotaInv n),
    S.iota_iotaInv (S.mem_range_of_mem_ker (by rw [AddMonoidHom.mem_ker, h0])),
    S.iota_cocycleOf]

/-! ## The connecting map -/

/-- A lift of `p ∈ P^G` to `N`. -/
noncomputable def liftOf (S : ShortExactSeq G M N P) (p : H0 G P) : N :=
  Classical.choose (S.pi_surjective (p : P))

theorem pi_liftOf (S : ShortExactSeq G M N P) (p : H0 G P) :
    S.pi (S.liftOf p) = (p : P) :=
  Classical.choose_spec (S.pi_surjective (p : P))

theorem liftOf_invariant (S : ShortExactSeq G M N P) (p : H0 G P) :
    (S.pi (S.liftOf p)) ∈ H0 G P := by
  rw [S.pi_liftOf]
  exact p.2

/-- **The connecting map** `δ : H⁰(G,P) → H¹(G,M)`: `p ↦ [g ↦ ι⁻¹(g • n - n)]` for a lift `n`
of `p`. -/
noncomputable def delta (S : ShortExactSeq G M N P) : H0 G P →+ H1 G M where
  toFun p := H1π G M (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p))
  map_zero' := by
    show H1π G M (S.cocycleOf (S.liftOf 0) (S.liftOf_invariant 0)) = 0
    rw [H1π_eq_zero_iff]
    exact S.mem_B1_cocycleOf_of_pi_eq_zero (S.liftOf_invariant 0)
      (by rw [S.pi_liftOf]; rfl)
  map_add' p q := by
    show H1π G M (S.cocycleOf (S.liftOf (p + q)) (S.liftOf_invariant (p + q))) =
      H1π G M (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p)) +
      H1π G M (S.cocycleOf (S.liftOf q) (S.liftOf_invariant q))
    rw [← map_add (H1π G M), ← S.cocycleOf_add (S.liftOf_invariant p) (S.liftOf_invariant q)]
    exact S.class_eq (S.liftOf_invariant (p + q))
      (S.mem_H0_pi_add (S.liftOf_invariant p) (S.liftOf_invariant q)) (by
      rw [S.pi_liftOf, map_add, S.pi_liftOf, S.pi_liftOf]
      rfl)

theorem delta_apply (S : ShortExactSeq G M N P) (p : H0 G P) :
    S.delta p = H1π G M (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p)) := rfl

/-! ## The two exactness inclusions -/

/-- The composite `H⁰(G,N) → H⁰(G,P) → H¹(G,M)` vanishes. -/
theorem delta_mapH0 (S : ShortExactSeq G M N P) (x : H0 G N) :
    S.delta (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant x) = 0 := by
  let p : H0 G P := Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant x
  show S.delta p = 0
  rw [S.delta_apply]
  have hclass : H1π G M (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p)) =
      H1π G M (S.cocycleOf (x : N) p.2) :=
    S.class_eq (S.liftOf_invariant p) p.2 (S.pi_liftOf p)
  rw [hclass, S.cocycleOf_eq_zero p.2 x.2, map_zero]

/-- The composite `H⁰(G,P) → H¹(G,M) → H¹(G,N)` vanishes. -/
theorem mapH1_iota_delta (S : ShortExactSeq G M N P) (p : H0 G P) :
    mapH1 S.iota S.iota_equivariant (S.delta p) = 0 := by
  rw [S.delta_apply, mapH1_H1π, H1π_eq_zero_iff]
  refine (Work.AbsoluteKummer.mem_B1_iff _).mpr ⟨S.liftOf p, ?_⟩
  show Work.GroupCohomology.d0 G N (S.liftOf p) =
    ((mapZ1 S.iota S.iota_equivariant (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p)) :
      Z1 G N) : G → N)
  funext g
  rw [Work.GroupCohomology.d0_apply, mapZ1_apply, S.iota_cocycleOf]

/-- **Exactness at `H⁰(G,P)`**: the image of `H⁰(G,N)` is contained in the kernel of `δ`. -/
theorem range_mapH0_le_ker_delta (S : ShortExactSeq G M N P) :
    (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range ≤ S.delta.ker := by
  rintro p ⟨x, rfl⟩
  rw [AddMonoidHom.mem_ker]
  exact S.delta_mapH0 x

/-- **Exactness at `H¹(G,M)`**: the image of `δ` is contained in the kernel of the map induced by
`ι`. -/
theorem range_delta_le_ker_mapH1 (S : ShortExactSeq G M N P) :
    S.delta.range ≤ (mapH1 S.iota S.iota_equivariant).ker := by
  rintro x ⟨p, rfl⟩
  rw [AddMonoidHom.mem_ker]
  exact S.mapH1_iota_delta p

end

end Work.AbsoluteKummer.ShortExactSeq
