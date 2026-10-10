import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.AlphaTwoDevissageAux
import Submission.Work.SSGRoute.PT.alphaConnectingCompat
import Submission.Work.SSGRoute.PT.five_lemma_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `α¹`-layer of Milne's class-formation theorem (`ADT` I.1.8, `r = 1`)

Milne's class-formation theorem (*Arithmetic Duality Theorems*, Theorem I.1.8) attaches to a finite
`G`-module `N` and a class formation `(G,C)` the maps

  `α^r(N) : Ext^r_G(N,C) ⟶ H^{2-r}(G,N)^∨ ,`

the two ends being `α⁰` (postcomposition with an equivariant hom) and `α²` (cupping with an
invariant element).  In the coefficient model of `PT/AlphaPairing.lean` (`C` divisible, so that
`Ext^r_G(N,C) = H^r(G, Hom_ℤ(N,C))` by Milne (0.8)) these are

* `alphaZero` — proved there;
* `alphaTwo : H²(G, Hom_ℤ(N,C)) →+ (N^G →+ H²(G,C))` — proved there;

and the `r = 1` map is the **evaluation cup of two `1`-cocycles**,

  `α¹(c) = (b ↦ c ⌣ b) : H¹(G, Hom_ℤ(N,C)) →+ (H¹(G,N) →+ H²(G,C))`.

This module supplies that map (`alphaOneMap`) together with its two descent steps and the
cocycle-level computation rule.  The cochain algebra it consumes is in
`PT/alphaConnectingCompat.lean`:

* `cupConn11 c b (g,h) = c g (g • b h)` — the `(1,1)`-evaluation cup;
* `cupConn11_mem_Z2` — the cup of two `1`-cocycles is a `2`-cocycle (algebraic part);
* `cupConn11_of_d1_eq_zero` — cupping with a `1`-**coboundary** in the second variable is a
  `2`-coboundary (`c ⌣ d⁰n = -d¹(c ⌣ n)`);
* `cupConn11_d0_eq` — cupping a `1`-**coboundary** in the first variable with a `1`-cocycle is a
  `2`-coboundary (`d⁰x ⌣ b = d¹(x ⌣ b)`);
* `cupConn11_add_left` / `cupConn11_add_right` — additivity in both variables.

What has to be added for the *continuous* model (`Work.AbsoluteKummer.Z2 = Z² ⊓ C²_c`,
`B2 = d¹(C¹_c)`) is the local-constancy bookkeeping: the evaluation cups of locally constant
cochains are locally constant (`cupConn11_isLocallyConstant`, `cupConn10_isLocallyConstant`,
`cupConn01_isLocallyConstant`).  With it, the cup of two *continuous* `1`-cocycles is a continuous
`2`-cocycle (`cupZ2`), it lands in `B²_c` whenever one of the two arguments is a coboundary
(`cupConn11_mem_B2_of_mem_B1_right`, `cupConn11_mem_B2_of_mem_B1_left`), and hence descends to

  `alphaOneMap (hN) : H¹(G, Hom_ℤ(N,C)) →+ (H¹(G,N) →+ H²(G,C))`

with the computation rule `alphaOneMap_H1π`.

## Why this is on the critical path

`h4` — the perfectness of the local Tate pairing in degree one, the last arithmetic input of
`G1 = Work.SSGRoute.canonical_localPairing_with_reciprocity` — *is* the bijectivity of
`α¹(M^∨(1))` (see `SSGRoute/E7Fin/H4_VIA_MILNE18.md` §1), and `G1` is one of the three remaining
holes of the final theorem (`SSGRoute/STATUS_node_properStageAssemblyData.md` §3).  This file
deliberately duplicates no arithmetic: it is the `r = 1` analogue of the proved `r = 2` layer
(`PT/AlphaPairing.lean`, `PT/AlphaTwoDevissage.lean`).
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical Filter

namespace Work.SSGRoute.PT

universe u v w

section Continuity

variable {G : Type u} [TopologicalSpace G] [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **The `(1,1)`-evaluation cup of locally constant cochains is locally constant.**  The
discreteness of `N` is exactly what freezes `g • b h` in a neighbourhood of `(g₀,h₀)`. -/
theorem cupConn11_isLocallyConstant [IsTopologicalGroup G]
    (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    {c : G → ConjHom N C} {b : G → N}
    (hc : Work.AbsoluteKummer.IsLocallyConstant c)
    (hb : Work.AbsoluteKummer.IsLocallyConstant b) :
    Work.AbsoluteKummer.IsLocallyConstant (fun p : G × G => cupConn11 c b p) := by
  rintro ⟨g₀, h₀⟩
  obtain ⟨U, hUo, hgU, hUc⟩ := hc g₀
  obtain ⟨V, hVo, hhV, hVc⟩ := hb h₀
  refine ⟨(U ∩ {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G (b h₀)}) ×ˢ V,
    (hUo.inter (Work.AbsoluteKummer.isOpen_smul_stabilizer hN g₀ (b h₀))).prod hVo,
    ⟨⟨hgU, Work.AbsoluteKummer.mem_self_smul_stabilizer g₀ (b h₀)⟩, hhV⟩, ?_⟩
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  obtain ⟨hgU, hgW⟩ := hg
  have hbh : b h = b h₀ := hVc h hh
  have hsm : g • b h₀ = g₀ • b h₀ :=
    Work.AbsoluteKummer.smul_eq_of_mem_smul_stabilizer hgW
  show c g (g • b h) = c g₀ (g₀ • b h₀)
  rw [hbh, hUc g hgU, hsm]

/-- **The `(1,0)`-evaluation cup of a locally constant cochain is locally constant.** -/
theorem cupConn10_isLocallyConstant [IsTopologicalGroup G]
    (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    {c : G → ConjHom N C} (hc : Work.AbsoluteKummer.IsLocallyConstant c) (n : N) :
    Work.AbsoluteKummer.IsLocallyConstant (fun g : G => cupConn10 c n g) := by
  intro g₀
  obtain ⟨U, hUo, hgU, hUc⟩ := hc g₀
  refine ⟨U ∩ {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G n},
    hUo.inter (Work.AbsoluteKummer.isOpen_smul_stabilizer hN g₀ n),
    ⟨hgU, Work.AbsoluteKummer.mem_self_smul_stabilizer g₀ n⟩, ?_⟩
  rintro g ⟨hgU, hgW⟩
  show c g (g • n) = c g₀ (g₀ • n)
  rw [hUc g hgU, Work.AbsoluteKummer.smul_eq_of_mem_smul_stabilizer hgW]

/-- **The `(0,1)`-evaluation cup of a locally constant cochain is locally constant.** -/
theorem cupConn01_isLocallyConstant {x : ConjHom N C} {b : G → N}
    (hb : Work.AbsoluteKummer.IsLocallyConstant b) :
    Work.AbsoluteKummer.IsLocallyConstant (fun g : G => cupConn01 x b g) := by
  intro g₀
  obtain ⟨V, hVo, hgV, hVc⟩ := hb g₀
  exact ⟨V, hVo, hgV, fun g hg => by
    show x (b g) = x (b g₀)
    rw [hVc g hg]⟩

end Continuity

/-! ## The cup of two continuous `1`-cocycles -/

section CupZ2

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- The cup of two **continuous** `1`-cocycles is a continuous `2`-cocycle. -/
theorem cupConn11_mem_Z2c (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    {c : G → ConjHom N C} {b : G → N}
    (hc : c ∈ Work.AbsoluteKummer.Z1 G (ConjHom N C))
    (hb : b ∈ Work.AbsoluteKummer.Z1 G N) :
    cupConn11 c b ∈ Work.AbsoluteKummer.Z2 G C := by
  obtain ⟨hc1, hc2⟩ := (Work.AbsoluteKummer.mem_Z1_iff c).mp hc
  obtain ⟨hb1, hb2⟩ := (Work.AbsoluteKummer.mem_Z1_iff b).mp hb
  refine ⟨?_, ?_⟩
  · exact cupConn11_mem_Z2 (c := c) (b := b)
      ((Work.GroupCohomology.mem_Z1_iff G (ConjHom N C) c).mpr hc1)
      ((Work.GroupCohomology.mem_Z1_iff G N b).mpr hb1)
  · exact cupConn11_isLocallyConstant hN hc2 hb2

/-- The `(1,1)`-cup of continuous `1`-cocycles, as an element of `Z²_c(G,C)`. -/
noncomputable def cupZ2 (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b : Work.AbsoluteKummer.Z1 G N) :
    Work.AbsoluteKummer.Z2 G C :=
  ⟨cupConn11 (c : G → ConjHom N C) (b : G → N), cupConn11_mem_Z2c hN c.2 b.2⟩

@[simp] theorem cupZ2_coe (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b : Work.AbsoluteKummer.Z1 G N) :
    ((cupZ2 hN c b : Work.AbsoluteKummer.Z2 G C) : G × G → C)
      = cupConn11 (c : G → ConjHom N C) (b : G → N) := rfl

theorem cupZ2_add_right (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b b' : Work.AbsoluteKummer.Z1 G N) :
    cupZ2 hN c (b + b') = cupZ2 hN c b + cupZ2 hN c b' :=
  Subtype.ext (by
    show cupConn11 (c : G → ConjHom N C) ((b : G → N) + (b' : G → N))
      = cupConn11 (c : G → ConjHom N C) (b : G → N)
        + cupConn11 (c : G → ConjHom N C) (b' : G → N)
    rw [cupConn11_add_right])

theorem cupZ2_add_left (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c c' : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b : Work.AbsoluteKummer.Z1 G N) :
    cupZ2 hN (c + c') b = cupZ2 hN c b + cupZ2 hN c' b :=
  Subtype.ext (by
    show cupConn11 ((c : G → ConjHom N C) + (c' : G → ConjHom N C)) (b : G → N)
      = cupConn11 (c : G → ConjHom N C) (b : G → N)
        + cupConn11 (c' : G → ConjHom N C) (b : G → N)
    rw [cupConn11_add_left])

end CupZ2

/-! ## The two descent steps of `α¹` -/

section Descent

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

theorem d1_eq_zero_of_mem_Z1c {c : G → ConjHom N C}
    (hc : c ∈ Work.AbsoluteKummer.Z1 G (ConjHom N C)) :
    Work.GroupCohomology.d1 G (ConjHom N C) c = 0 := by
  have hmem : c ∈ Work.GroupCohomology.Z1 G (ConjHom N C) :=
    (Work.AbsoluteKummer.mem_Z1_iff c).mp hc |>.1 |>
      (Work.GroupCohomology.mem_Z1_iff G (ConjHom N C) c).mpr
  rw [Work.GroupCohomology.Z1_eq_ker_d1 G (ConjHom N C)] at hmem
  exact AddMonoidHom.mem_ker.mp hmem

/-- **Second descent step of `α¹`**: cupping a continuous `1`-cocycle with a **coboundary** in the
second variable is a continuous `2`-coboundary. -/
theorem cupConn11_mem_B2_of_mem_B1_right (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    {c : G → ConjHom N C} (hc : c ∈ Work.AbsoluteKummer.Z1 G (ConjHom N C))
    {b : G → N} (hb : b ∈ Work.AbsoluteKummer.B1 G N) :
    cupConn11 c b ∈ Work.AbsoluteKummer.B2 G C := by
  obtain ⟨n, rfl⟩ := (Work.AbsoluteKummer.mem_B1_iff b).mp hb
  have hc1 : Work.GroupCohomology.d1 G (ConjHom N C) c = 0 := d1_eq_zero_of_mem_Z1c hc
  rw [cupConn11_of_d1_eq_zero c n hc1]
  refine AddSubgroup.neg_mem _ ?_
  refine AddSubgroup.mem_map.mpr ⟨cupConn10 c n, ?_, rfl⟩
  exact (Work.AbsoluteKummer.mem_C1c_iff _).mpr
    (cupConn10_isLocallyConstant hN ((Work.AbsoluteKummer.mem_Z1_iff c).mp hc).2 n)

/-- **First descent step of `α¹`**: cupping a **coboundary** in the first variable with a
continuous `1`-cocycle is a continuous `2`-coboundary. -/
theorem cupConn11_mem_B2_of_mem_B1_left (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    {c : G → ConjHom N C} (hc : c ∈ Work.AbsoluteKummer.B1 G (ConjHom N C))
    {b : G → N} (hb : b ∈ Work.AbsoluteKummer.Z1 G N) :
    cupConn11 c b ∈ Work.AbsoluteKummer.B2 G C := by
  obtain ⟨x, rfl⟩ := (Work.AbsoluteKummer.mem_B1_iff c).mp hc
  have hb1 : Work.GroupCohomology.d1 G N b = 0 := by
    have hmem : b ∈ Work.GroupCohomology.Z1 G N :=
      (Work.AbsoluteKummer.mem_Z1_iff b).mp hb |>.1 |> (Work.GroupCohomology.mem_Z1_iff G N b).mpr
    rw [Work.GroupCohomology.Z1_eq_ker_d1 G N] at hmem
    exact AddMonoidHom.mem_ker.mp hmem
  rw [cupConn11_d0_eq x b hb1]
  refine AddSubgroup.mem_map.mpr ⟨cupConn01 x b, ?_, rfl⟩
  exact (Work.AbsoluteKummer.mem_C1c_iff _).mpr
    (cupConn01_isLocallyConstant ((Work.AbsoluteKummer.mem_Z1_iff b).mp hb).2)

end Descent

/-! ## The map `α¹ : H¹(G, Hom_ℤ(N,C)) →+ (H¹(G,N) →+ H²(G,C))` -/

section AlphaOneMap

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- The cupping with a fixed continuous `1`-cocycle `c`, as an additive map out of `Z¹_c(G,N)`. -/
noncomputable def alphaOneFun (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) :
    Work.AbsoluteKummer.Z1 G N →+ Work.AbsoluteKummer.H2 G C where
  toFun b := Work.AbsoluteKummer.H2π G C (cupZ2 hN c b)
  map_zero' := by
    show Work.AbsoluteKummer.H2π G C (cupZ2 hN c 0) = 0
    rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
    show cupConn11 (c : G → ConjHom N C)
      ((0 : Work.AbsoluteKummer.Z1 G N) : G → N) ∈ Work.AbsoluteKummer.B2 G C
    rw [show ((0 : Work.AbsoluteKummer.Z1 G N) : G → N) = 0 from rfl, cupConn11_zero_right]
    exact (Work.AbsoluteKummer.B2 G C).zero_mem
  map_add' b b' := by
    show Work.AbsoluteKummer.H2π G C (cupZ2 hN c (b + b'))
      = Work.AbsoluteKummer.H2π G C (cupZ2 hN c b)
        + Work.AbsoluteKummer.H2π G C (cupZ2 hN c b')
    rw [cupZ2_add_right, map_add]

@[simp] theorem alphaOneFun_apply (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b : Work.AbsoluteKummer.Z1 G N) :
    alphaOneFun hN c b = Work.AbsoluteKummer.H2π G C (cupZ2 hN c b) := rfl

/-- The cup, as an additive map on `Z¹_c(G, Hom_ℤ(N,C))` with values in the additive maps out of
`H¹(G,N)`: the descent in the second variable. -/
noncomputable def alphaOneZ (hN : Work.AbsoluteKummer.IsDiscreteModule G N) :
    Work.AbsoluteKummer.Z1 G (ConjHom N C) →+
      (Work.AbsoluteKummer.H1 G N →+ Work.AbsoluteKummer.H2 G C) where
  toFun c := QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B1 G N).comap (Work.AbsoluteKummer.Z1 G N).subtype)
    (alphaOneFun hN c)
    (by
      intro x hx
      have hx' : ((x : Work.AbsoluteKummer.Z1 G N) : G → N) ∈ Work.AbsoluteKummer.B1 G N :=
        AddSubgroup.mem_comap.mp hx
      show alphaOneFun hN c x = 0
      rw [alphaOneFun_apply, Work.AbsoluteKummer.H2π_eq_zero_iff]
      exact cupConn11_mem_B2_of_mem_B1_right hN c.2 hx')
  map_zero' := by
    refine AddMonoidHom.ext fun b => ?_
    obtain ⟨b', rfl⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 G N).comap (Work.AbsoluteKummer.Z1 G N).subtype) b
    show Work.AbsoluteKummer.H2π G C (cupZ2 hN 0 b') = 0
    rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
    show cupConn11 ((0 : Work.AbsoluteKummer.Z1 G (ConjHom N C)) : G → ConjHom N C)
      (b' : G → N) ∈ Work.AbsoluteKummer.B2 G C
    rw [show ((0 : Work.AbsoluteKummer.Z1 G (ConjHom N C)) : G → ConjHom N C) = 0 from rfl,
      cupConn11_zero_left (b' : G → N)]
    exact (Work.AbsoluteKummer.B2 G C).zero_mem
  map_add' c c' := by
    refine AddMonoidHom.ext fun b => ?_
    obtain ⟨b', rfl⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 G N).comap (Work.AbsoluteKummer.Z1 G N).subtype) b
    show Work.AbsoluteKummer.H2π G C (cupZ2 hN (c + c') b')
      = Work.AbsoluteKummer.H2π G C (cupZ2 hN c b') + Work.AbsoluteKummer.H2π G C (cupZ2 hN c' b')
    rw [cupZ2_add_left, map_add]

/-- **The `r = 1` class-formation map `α¹`** : cupping with a continuous `1`-cocycle of
`Hom_ℤ(N,C)`, as an additive map `H¹(G, Hom_ℤ(N,C)) →+ (H¹(G,N) →+ H²(G,C))`. -/
noncomputable def alphaOneMap (hN : Work.AbsoluteKummer.IsDiscreteModule G N) :
    Work.AbsoluteKummer.H1 G (ConjHom N C) →+
      (Work.AbsoluteKummer.H1 G N →+ Work.AbsoluteKummer.H2 G C) :=
  QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B1 G (ConjHom N C)).comap
      (Work.AbsoluteKummer.Z1 G (ConjHom N C)).subtype)
    (alphaOneZ hN)
    (by
      intro x hx
      have hx' : ((x : Work.AbsoluteKummer.Z1 G (ConjHom N C)) : G → ConjHom N C)
          ∈ Work.AbsoluteKummer.B1 G (ConjHom N C) := AddSubgroup.mem_comap.mp hx
      show alphaOneZ hN x = 0
      refine AddMonoidHom.ext fun b => ?_
      obtain ⟨b', rfl⟩ := QuotientAddGroup.mk'_surjective
        ((Work.AbsoluteKummer.B1 G N).comap (Work.AbsoluteKummer.Z1 G N).subtype) b
      show Work.AbsoluteKummer.H2π G C (cupZ2 hN x b') = 0
      rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
      exact cupConn11_mem_B2_of_mem_B1_left hN hx' b'.2)

/-- The computation rule of the inner descent: on a `1`-cocycle `b`, `α¹(c)` is the class of the
cup. -/
theorem alphaOneZ_H1π (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b : Work.AbsoluteKummer.Z1 G N) :
    alphaOneZ hN c (Work.AbsoluteKummer.H1π G N b) = alphaOneFun hN c b := rfl

/-- The computation rule of the outer descent. -/
theorem alphaOneMap_H1π_Z (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) :
    alphaOneMap hN (Work.AbsoluteKummer.H1π G (ConjHom N C) c) = alphaOneZ hN c := rfl



/-- The computation rule of `α¹` on `1`-cocycles. -/
theorem alphaOneMap_H1π (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom N C)) (b : Work.AbsoluteKummer.Z1 G N) :
    alphaOneMap hN (Work.AbsoluteKummer.H1π G (ConjHom N C) c)
        (Work.AbsoluteKummer.H1π G N b)
      = Work.AbsoluteKummer.H2π G C (cupZ2 hN c b) := by
  rw [alphaOneMap_H1π_Z hN c, alphaOneZ_H1π hN c b]
  rfl

/-- **Naturality of `α¹` in the coefficient module** (the `r = 1` companion of
`PT.alphaTwo_naturality`): for an equivariant `φ : N₁ →+ N₂`, pulling `x` back along
`ConjHom.precomp φ` and pushing `b` forward along `φ` give the same value.  This is the first two
columns of Milne's diagram (1.9.1) at `r = 1`. -/
theorem alphaOneMap_naturalityPrecomp {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {N₁ : Type u} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type u} [AddCommGroup N₂] [DistribMulAction G N₂]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C]
    (hN₁ : Work.AbsoluteKummer.IsDiscreteModule G N₁)
    (hN₂ : Work.AbsoluteKummer.IsDiscreteModule G N₂)
    (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpre : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ))
    (x : Work.AbsoluteKummer.H1 G (ConjHom N₂ C)) (b : Work.AbsoluteKummer.H1 G N₁) :
    alphaOneMap hN₂ x (Work.AbsoluteKummer.mapH1 φ hφ b)
      = alphaOneMap hN₁
          (Work.AbsoluteKummer.mapH1 (ConjHom.precomp (C := C) φ) hpre x) b := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 G (ConjHom N₂ C)).comap
      (Work.AbsoluteKummer.Z1 G (ConjHom N₂ C)).subtype) x
  obtain ⟨b', hb'⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 G N₁).comap (Work.AbsoluteKummer.Z1 G N₁).subtype) b
  rw [show x = Work.AbsoluteKummer.H1π G (ConjHom N₂ C) c from hc.symm,
    show b = Work.AbsoluteKummer.H1π G N₁ b' from hb'.symm,
    Work.AbsoluteKummer.mapH1_H1π, Work.AbsoluteKummer.mapH1_H1π,
    alphaOneMap_H1π hN₂ c, alphaOneMap_H1π hN₁]
  refine congrArg (Work.AbsoluteKummer.H2π G C) (Subtype.ext ?_)
  show cupConn11 (c : G → ConjHom N₂ C) (fun g => φ ((b' : G → N₁) g))
      = cupConn11 (fun g => ConjHom.precomp (C := C) φ ((c : G → ConjHom N₂ C) g))
          ((b' : G → N₁))
  exact (cupConn11_precomp φ hφ (c : G → ConjHom N₂ C) (b' : G → N₁)).symm


section Descent

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {N : Type u} [AddCommGroup N] [DistribMulAction G N]
  {N₁ : Type u} [AddCommGroup N₁] [DistribMulAction G N₁]
  {N₂ : Type u} [AddCommGroup N₂] [DistribMulAction G N₂]
  {C : Type u} [AddCommGroup C] [DistribMulAction G C]

/-- Composition with `f` as an additive map of the (additive) hom-groups: the transpose
`(M →+ X) →+ (L →+ X)` of `f : L →+ M`.  (A local copy of `PT.precompHom`, so that the descent's
statement does not depend on the argument names of that definition.) -/
def transp {L M X : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup X]
    (f : L →+ M) : (M →+ X) →+ (L →+ X) := precompHom f

@[simp] theorem transp_apply {L M X : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup X]
    (f : L →+ M) (ψ : M →+ X) : transp f ψ = ψ.comp f := rfl

/-- The outer vertical maps of the bottom row of Milne's diagram, as named definitions (so that the
statement of `alphaOne_bijective_of_devissage` needs no type ascriptions). -/
noncomputable def transpMapH1 (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ) :
    (Work.AbsoluteKummer.H1 G N₁ →+ Work.AbsoluteKummer.H2 G C) →+
      (Work.AbsoluteKummer.H1 G N₂ →+ Work.AbsoluteKummer.H2 G C) :=
  transp (X := Work.AbsoluteKummer.H2 G C) (Work.AbsoluteKummer.mapH1 ψ hψ)

noncomputable def transpMapH1' (φ : N →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    (Work.AbsoluteKummer.H1 G N₂ →+ Work.AbsoluteKummer.H2 G C) →+
      (Work.AbsoluteKummer.H1 G N →+ Work.AbsoluteKummer.H2 G C) :=
  transp (X := Work.AbsoluteKummer.H2 G C) (Work.AbsoluteKummer.mapH1 φ hφ)

noncomputable def transpDelta (δm : Work.AbsoluteKummer.H0 G N₁ →+ Work.AbsoluteKummer.H1 G N) :
    (Work.AbsoluteKummer.H1 G N →+ Work.AbsoluteKummer.H2 G C) →+
      (Work.AbsoluteKummer.H0 G N₁ →+ Work.AbsoluteKummer.H2 G C) :=
  transp (X := Work.AbsoluteKummer.H2 G C) δm

noncomputable def transpInvariants (ψ : N₂ →+ N₁)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) :
    (Work.AbsoluteKummer.H0 G N₁ →+ Work.AbsoluteKummer.H2 G C) →+
      (Work.AbsoluteKummer.H0 G N₂ →+ Work.AbsoluteKummer.H2 G C) :=
  transp (X := Work.AbsoluteKummer.H2 G C) (invariantsHom ψ hψ)


/-- **The `r = 1` five-lemma descent of Milne's class-formation theorem.**

Milne (*ADT*, I.1.8, diagram (1.9.1)) descends `α¹` along a short exact sequence of coefficients
`0 → N → N₂ → N₁ → 0` (ι = `φ`, π = `ψ`; in the application `N₂ = Coind_U^G N`).  The ladder at
`r = 1` is

    H¹(Hom(N₁,C)) --mapH1 (precomp ψ)--> H¹(Hom(N₂,C)) --mapH1 (precomp φ)--> H¹(Hom(N,C))
      --δc--> H²(Hom(N₁,C)) --mapH2 (precomp ψ)--> H²(Hom(N₂,C))
       ↓ α¹                ↓ α¹                ↓ α¹           ↓ α²                 ↓ α²
    (H¹(N₁))^∨ --precompHom (mapH1 ψ)--> (H¹(N₂))^∨ --precompHom (mapH1 φ)--> (H¹(N))^∨
      --precompHom δm--> (H⁰(N₁))^∨ --precompHom (invariantsHom ψ)--> (H⁰(N₂))^∨

(`(X)^∨ = X →+ H²(G,C)`, `δc` the connecting map of the coefficient short exact sequence
`0 → Hom(N₁,C) → Hom(N₂,C) → Hom(N,C) → 0`, `δm` the connecting map of
`0 → N → N₂ → N₁ → 0`).  If both rows are exact, the third square commutes (the **Leibniz rule**
`α²(δc z)(n) = α¹(z)(δm n)`, the cochain form of which is `SES_cupConn_sub_mem_B2`), and the four
*outer* verticals are bijective, then the middle vertical `α¹(G,N)` is bijective.  The first,
second and fourth squares are *not* hypotheses: they are the proved naturalities
`alphaOneMap_naturalityPrecomp` (for `ψ` and for `φ`) and `PT.alphaTwo_naturality` (for `ψ`). -/
theorem alphaOne_bijective_of_devissage
    (hN : Work.AbsoluteKummer.IsDiscreteModule G N)
    (hN₁ : Work.AbsoluteKummer.IsDiscreteModule G N₁)
    (hN₂ : Work.AbsoluteKummer.IsDiscreteModule G N₂)
    (φ : N →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpreφ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ))
    (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hpreψ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) ψ))
    (δc : Work.AbsoluteKummer.H1 G (ConjHom N C) →+ Work.AbsoluteKummer.H2 G (ConjHom N₁ C))
    (δm : Work.AbsoluteKummer.H0 G N₁ →+ Work.AbsoluteKummer.H1 G N)
    (hleib : ∀ (z : Work.AbsoluteKummer.H1 G (ConjHom N C)) (n : Work.AbsoluteKummer.H0 G N₁),
      alphaTwo (G := G) (N := N₁) (C := C) (δc z) n = alphaOneMap hN z (δm n))
    (etop₁ : Function.Exact (Work.AbsoluteKummer.mapH1 (ConjHom.precomp (C := C) ψ) hpreψ)
      (Work.AbsoluteKummer.mapH1 (ConjHom.precomp (C := C) φ) hpreφ))
    (etop₂ : Function.Exact (Work.AbsoluteKummer.mapH1 (ConjHom.precomp (C := C) φ) hpreφ) δc)
    (etop₃ : Function.Exact δc (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) ψ) hpreψ))
    (ebot₁ : Function.Exact (transpMapH1 (G := G) (N₁ := N₁) (N₂ := N₂) (C := C) ψ hψ)
      (transpMapH1' (G := G) (N := N) (N₂ := N₂) (C := C) φ hφ))
    (ebot₂ : Function.Exact (transpMapH1' (G := G) (N := N) (N₂ := N₂) (C := C) φ hφ)
      (transpDelta (G := G) (N := N) (N₁ := N₁) (C := C) δm))
    (ebot₃ : Function.Exact (transpDelta (G := G) (N := N) (N₁ := N₁) (C := C) δm)
      (transpInvariants (G := G) (N₁ := N₁) (N₂ := N₂) (C := C) ψ hψ))
    (hα₁ : Function.Bijective (alphaOneMap (G := G) (N := N₁) (C := C) hN₁))
    (hα₂ : Function.Bijective (alphaOneMap (G := G) (N := N₂) (C := C) hN₂))
    (hβ₁ : Function.Bijective (alphaTwo (G := G) (N := N₁) (C := C)))
    (hβ₂ : Function.Bijective (alphaTwo (G := G) (N := N₂) (C := C))) :
    Function.Bijective (alphaOneMap (G := G) (N := N) (C := C) hN) := by
  refine five_lemma_exact
    (f1 := Work.AbsoluteKummer.mapH1 (ConjHom.precomp (C := C) ψ) hpreψ)
    (f2 := Work.AbsoluteKummer.mapH1 (ConjHom.precomp (C := C) φ) hpreφ)
    (f3 := δc)
    (f4 := Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) ψ) hpreψ)
    (g1 := transpMapH1 (G := G) (N₁ := N₁) (N₂ := N₂) (C := C) ψ hψ)
    (g2 := transpMapH1' (G := G) (N := N) (N₂ := N₂) (C := C) φ hφ)
    (g3 := transpDelta (G := G) (N := N) (N₁ := N₁) (C := C) δm)
    (g4 := transpInvariants (G := G) (N₁ := N₁) (N₂ := N₂) (C := C) ψ hψ)
    (a1 := alphaOneMap (G := G) (N := N₁) (C := C) hN₁)
    (a2 := alphaOneMap (G := G) (N := N₂) (C := C) hN₂)
    (a3 := alphaOneMap (G := G) (N := N) (C := C) hN)
    (a4 := alphaTwo (G := G) (N := N₁) (C := C))
    (a5 := alphaTwo (G := G) (N := N₂) (C := C))
    ?_ ?_ ?_ ?_ etop₁ etop₂ etop₃ ebot₁ ebot₂ ebot₃ hα₁.2 hα₂ hβ₁ hβ₂.1
  · intro x
    exact AddMonoidHom.ext fun y =>
      (alphaOneMap_naturalityPrecomp (N₁ := N₂) (N₂ := N₁) hN₂ hN₁ ψ hψ hpreψ x y).symm
  · intro x
    exact AddMonoidHom.ext fun y =>
      (alphaOneMap_naturalityPrecomp (N₁ := N) (N₂ := N₂) hN hN₂ φ hφ hpreφ x y).symm
  · intro x
    exact AddMonoidHom.ext (hleib x)
  · intro x
    exact AddMonoidHom.ext fun n =>
      alphaTwo_naturality ψ hψ hpreψ x n

end Descent

end AlphaOneMap

end Work.SSGRoute.PT
