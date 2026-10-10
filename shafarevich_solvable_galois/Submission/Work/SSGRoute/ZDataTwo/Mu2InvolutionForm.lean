import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDArch.Defs
import Submission.Work.SSGRoute.ZDataTwo.Mu2ArchReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local form of the `μ₂` local Tate system

At an involution `c` of `G_k = Ω ≃ₐ[k] Ω` (a complex conjugation, i.e. a real place, by
Artin–Schreier) the local group is `⟨c⟩ ≅ ℤ/2`; the coefficients are `ZMod 2` with the trivial
action (the action of `Gal(K/k)` on `ZMod 2` is trivial), so:

* the `1`-cocycles on `⟨c⟩` are the additive maps, i.e. the functions vanishing at `1`;
* the coboundaries on `⟨c⟩` are exactly the functions vanishing on `⟨c⟩`;
* hence the evaluation at `c` is well defined on the local cohomology
  `H1loc 2 k Ω K (ZMod 2) ⟨c⟩`, and it vanishes precisely on the classes that are non-zero…
  it is injective off `0` (a non-zero class has a representative with value `1` at `c`).

Consequently the pairing `Φ x y := (x c) * (y c)` is `𝔽₂`-bilinear and non-degenerate in both
variables, and on the classes of globally locally constant cocycles it computes `a c * b c` — the
archimedean invariant that enters the reciprocity clause of
`IsMu2LocalTateSystemWithArch`.
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]

/-- The elements of `Subgroup.zpowers c` for an involution `c` are `1` and `c`. -/
lemma mem_zpowers_eq_one_or (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ Subgroup.zpowers c) : g = 1 ∨ g = c := by
  let T : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {x | x = 1 ∨ x = c}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · rw [ha, hb, one_mul]; exact Or.inl rfl
        · rw [ha, hb, one_mul]; exact Or.inr rfl
        · rw [ha, hb, mul_one]; exact Or.inr rfl
        · rw [ha, hb, ← pow_two, hc]; exact Or.inl rfl
      inv_mem' := by
        rintro a (ha | ha)
        · rw [ha, inv_one]; exact Or.inl rfl
        · rw [ha, inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hc)]; exact Or.inr rfl }
  exact Subgroup.zpowers_le.mpr (show c ∈ T from Or.inr rfl) hg

variable {k Ω K}

/-- An additive function on an involution subgroup vanishes at `1`. -/
lemma eq_zero_one_of_cocycle_zpowers {c : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1)
    {f : (Ω ≃ₐ[k] Ω) → ZMod 2}
    (hf : ∀ g ∈ Subgroup.zpowers c, ∀ h ∈ Subgroup.zpowers c, f (g * h) = f g + f h) :
    f 1 = 0 := by
  have h := hf 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [mul_one] at h
  have h' : f 1 + f 1 = f 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

/-- **The evaluation at the involution is well defined on the local cohomology.**  Two locally
constant cocycles on `⟨c⟩` with the same class take the same value at `c`, because the
coboundaries on `⟨c⟩` vanish identically (the action on `ZMod 2` is trivial). -/
lemma eval_zpowers_wellDefined {c : Ω ≃ₐ[k] Ω} {f g : (Ω ≃ₐ[k] Ω) → ZMod 2}
    (hf : f ∈ lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c))
    (hg : g ∈ lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c))
    (h : toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers c) f
      = toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers c) g) : f c = g c := by
  have hq : (Submodule.mkQ (R := ZMod 2)
        (Submodule.comap (lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c)).subtype
          (coboundaries 2 k Ω K (ZMod 2) (Subgroup.zpowers c)))
        ⟨f, hf⟩ : H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c))
      = Submodule.mkQ (R := ZMod 2)
        (Submodule.comap (lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c)).subtype
          (coboundaries 2 k Ω K (ZMod 2) (Subgroup.zpowers c))) ⟨g, hg⟩ := by
    simpa only [toClass, dif_pos hf, dif_pos hg] using h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hq
  have hmem : (f - g) ∈ coboundaries 2 k Ω K (ZMod 2) (Subgroup.zpowers c) := by
    have h1 := (Submodule.Quotient.eq _).mp hq
    have h2 := Submodule.mem_comap.mp h1
    simpa using h2
  have hzero : (f - g) c = 0 := by
    have hcob : IsCoboundaryOn (res k K) (Subgroup.zpowers c) (fun x => f x - g x) :=
      (mem_coboundaries 2 k Ω K (ZMod 2) (Subgroup.zpowers c) (fun x => f x - g x)).mp hmem
    exact (isCoboundaryOn_iff_eq_zero k Ω K (Subgroup.zpowers c) (fun x => f x - g x)).mp hcob
      c (Subgroup.mem_zpowers c)
  simpa using sub_eq_zero.mp hzero

end Work.SSGRoute.ZDataTwo
