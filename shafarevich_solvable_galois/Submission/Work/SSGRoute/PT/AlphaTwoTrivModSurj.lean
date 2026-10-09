import Mathlib
import Submission.Work.SSGRoute.PT.AlphaTwoTrivModInj
import Submission.Work.SSGRoute.PT.AlphaTwoBaseCase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Surjectivity of `α²` on the trivial module, and the Kummer base case -/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- **Surjectivity of `α²` on the trivial module.** -/
theorem alphaTwo_trivMod_surjective {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) [Fact p.Prime] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C) (hSπ : ∀ c : C, S.pi c = p • c) :
    Function.Surjective (alphaTwo (G := G) (N := TrivMod G p) (C := C)) := by
  have hk1 : ((1 : ℤ) : TrivMod G p) ∈ Work.GroupCohomology.invariants G (TrivMod G p) := by
    simp [Work.GroupCohomology.invariants, TrivMod.smul_eq]
  have hgen0 : p • (⟨((1 : ℤ) : TrivMod G p), hk1⟩ :
      ↥(Work.GroupCohomology.invariants G (TrivMod G p))) = 0 := by
    refine Subtype.ext ?_
    simp
  intro f
  have hy : f ⟨((1 : ℤ) : TrivMod G p), hk1⟩ ∈ PTor p (Work.AbsoluteKummer.H2 G C) := by
    rw [mem_PTor, ← map_nsmul, hgen0, map_zero]
  obtain ⟨x, hx⟩ := mapH2_ptorEquiv_surjective (G := G) p S hSι hSπ
    ⟨f ⟨((1 : ℤ) : TrivMod G p), hk1⟩, hy⟩
  refine ⟨x, ?_⟩
  refine AddMonoidHom.ext (fun n => ?_)
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p) (n : TrivMod G p)
  have hn : n = k • (⟨((1 : ℤ) : TrivMod G p), hk1⟩ :
      ↥(Work.GroupCohomology.invariants G (TrivMod G p))) := by
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_zsmul, Subtype.coe_mk, zsmul_eq_mul]
    have hk' : ((k : ℤ) : TrivMod G p) = (n : TrivMod G p) := hk
    simpa using hk'.symm
  rw [hn, map_zsmul, map_zsmul]
  congr 1
  rw [alphaTwo_trivMod_apply_one (G := G) p x hk1]
  have hcongr := mapH2_congr_coeff
    (hφ := subtype_comp_conjHomTrivModEquivPTor_equivariant G p C)
    (hψ := evalOne_equivariant G p C)
    (h := subtype_comp_conjHomTrivModEquivPTor G p C)
  refine (congrArg (fun (φ : Work.AbsoluteKummer.H2 G (ConjHom (TrivMod G p) C) →+
      Work.AbsoluteKummer.H2 G C) => φ x) hcongr).symm.trans ?_
  rw [hx]

/-- **The Kummer base case**: `α²` on the trivial module is an isomorphism. -/
theorem alphaTwo_trivMod_bijective {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) [Fact p.Prime] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C) (hSπ : ∀ c : C, S.pi c = p • c)
    (h1 : Subsingleton (Work.AbsoluteKummer.H1 G C)) :
    Function.Bijective (alphaTwo (G := G) (N := TrivMod G p) (C := C)) :=
  ⟨alphaTwo_trivMod_injective (G := G) p S hSι h1,
    alphaTwo_trivMod_surjective (G := G) p S hSι hSπ⟩

end

end Work.SSGRoute.PT
