/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area

# `U_N ⊆ U_{\bar N}` for the `toUK`-structure map

Let `G` be a countable group, `H ≤ G`, `H₀ ≤ ↥H` and `N ≤ H₀`, and let

* `φ := (toUK U(G) (RingHom.id ℂ) H).toRingHom : ℂ[↥H] →+* U(G)` be the structure map of the
  concrete envelope `U(G)`, restricted to `ℂ[↥H]`;
* `U_N = Work.Section6.UN φ H₀ N` be the `∗`-regular closure of the image of
  `phiN φ H₀ N : ℂ[↥N] →+* U(G)` in `U(G)` (`φ` post-composed with the inclusions of group
  algebras `ℂ[↥N] → ℂ[↥H₀] → ℂ[↥H]`);
* `\bar N := (N.map H₀.subtype).map H.subtype ≤ G` be the image of `N` in `G`;
* `U_{\bar N} = Work.ORP311.closureCN \bar N` be the `∗`-regular closure of the image of
  `phiN \bar N : ℂ[↥\bar N] →+* U(G)`.

**Main result.**  `U_N ⊆ U_{\bar N}`.

This is the module that replaces the `sorry`-placeholder `hle` of
`Submission/Work/ORP311/prop311OnComplex.lean`: it compares the two `∗`-regular closures of
`ℂ[N]`-images that occur in the two formulations of JZLA20, Proposition 3.11.

## Proof

Both objects are `∗`-regular closures of the images of ring homomorphisms out of a group algebra,
so (`starRegularClosure_mono` composed with `starSubringClosure_mono`) it suffices to prove the
range inclusion
`Set.range (phiN φ H₀ N) ⊆ Set.range (phiN \bar N)`.

Write `f : ↥H₀ →* G` for the composite `H.subtype ∘ H₀.subtype`; then `\bar N = N.map f`
(`Subgroup.map_map`) and the canonical map `ψ : ↥N →* ↥M` (a `codRestrict` of `f ∘ N.subtype`)
satisfies `M.subtype ∘ ψ = f ∘ N.subtype`.  The key pointwise identity is
`phiN φ H₀ N = (phiN M).comp (mapDomainRingHom ℂ ψ)`, which reduces on generators to

* `φ (single h c) = iota G (single (h : G) c)` for `h : ↥H`, `c : ℂ`
  (`toUK_single` together with `E.ι (single g c) = c • genU E g`),
* `phiN M (single m c) = iota G (single (m : G) c)` for `m : ↥M`, `c : ℂ`.

The range inclusion then follows by exhibiting `mapDomainRingHom ℂ ψ x` as a preimage.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_mono
import Submission.Work.ORBridgeLinnell.Basic

set_option autoImplicit false

namespace Work.ORP311

open Work.ORVonNeumann

theorem UN_toUK_le_closureCN (G : Type) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) (H₀ : Subgroup ↥H) (N : Subgroup H₀) : ((Work.Section6.UN ((Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H).toRingHom) H₀ N : Work.ORHughesFree.StarSubring (Work.ORP311.concreteEnvelope G).U) : Set (Work.ORP311.concreteEnvelope G).U) ⊆ (Work.ORP311.closureCN ((N.map H₀.subtype).map H.subtype) : Set (Work.ORP311.concreteEnvelope G).U) := by
  set φ := (Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H).toRingHom
    with hφ
  set M : Subgroup G := (N.map H₀.subtype).map H.subtype with hMdef
  let f : ↥H₀ →* G := H.subtype.comp H₀.subtype
  have hM : M = N.map f := by rw [hMdef, Subgroup.map_map]
  let ψ : ↥N →* ↥M := (f.comp N.subtype).codRestrict M (fun n => by
    rw [hM]; exact Subgroup.mem_map_of_mem f n.2)
  -- the two basis formulas
  have hphiMsingle : ∀ (m : ↥M) (c : ℂ),
      Work.ORP311.phiN M (MonoidAlgebra.single m c) =
        Work.ORP311.iota G (MonoidAlgebra.single (m : G) c) := by
    intro m c
    simp only [Work.ORP311.phiN, RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    rfl
  have hφsingle : ∀ (h : ↥H) (c : ℂ),
      φ (MonoidAlgebra.single h c) = Work.ORP311.iota G (MonoidAlgebra.single (h : G) c) := by
    intro h c
    rw [hφ]
    change (Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H)
        (MonoidAlgebra.single h c) = Work.ORP311.iota G (MonoidAlgebra.single (h : G) c)
    rw [Work.ORBridgeLinnell.toUK_single, Work.ORP311.iota_apply]
    rw [show (Work.ORP311.concreteEnvelope G).ι (MonoidAlgebra.single (h : G) c)
        = c • Work.ORBridgeLinnell.genU (Work.ORP311.concreteEnvelope G) (h : G) from
      (by
        have hmul : MonoidAlgebra.single (h : G) (1 : ℂ) * MonoidAlgebra.single (1 : G) c
            = MonoidAlgebra.single (h : G) c := by
          rw [MonoidAlgebra.single_mul_single, mul_one, one_mul]
        have hone : MonoidAlgebra.single (1 : G) c
            = algebraMap ℂ (MonoidAlgebra ℂ G) c := by
          rw [MonoidAlgebra.coe_algebraMap]; rfl
        rw [← hmul, map_mul, hone, (Work.ORP311.concreteEnvelope G).ι_algebraMap,
          Work.ORBridgeLinnell.genU_apply]
        rw [Algebra.smul_def, Algebra.commutes])]
  -- the key identity of ring homomorphisms
  have hphi : Work.Section6.phiN φ H₀ N
      = (Work.ORP311.phiN M).comp (MonoidAlgebra.mapDomainRingHom ℂ ψ) := by
    refine MonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · simp only [Work.Section6.phiN, Work.ORHughesFree.inducedMapRing, RingHom.comp_apply,
        MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
      rw [hφsingle (H₀.subtype (N.subtype 1)) r, hphiMsingle (ψ 1) r]
      rfl
    · simp only [Work.Section6.phiN, Work.ORHughesFree.inducedMapRing, RingHom.comp_apply,
        MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
      rw [hφsingle (H₀.subtype (N.subtype m)) 1, hphiMsingle (ψ m) 1]
      rfl
  -- the range inclusion
  have hrange : Set.range (Work.Section6.phiN φ H₀ N) ⊆ Set.range (Work.ORP311.phiN M) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨MonoidAlgebra.mapDomainRingHom ℂ ψ x, ?_⟩
    show Work.ORP311.phiN M (MonoidAlgebra.mapDomainRingHom ℂ ψ x)
        = Work.Section6.phiN φ H₀ N x
    rw [← RingHom.comp_apply, ← hphi]
  -- assemble
  exact Work.ORHughesFree.StarRegular.starRegularClosure_mono
    (Work.ORHughesFree.StarRegular.starSubringClosure_mono hrange)

end Work.ORP311
