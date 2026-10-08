import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

set_option linter.unusedVariables false

/-- The squaring map `A/A² ≅ Ω₁(P)` is a bijective group homomorphism. -/
theorem c4nocard_nu_iso {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    [hN : ((Work.Higman.powSub A 2).subgroupOf A).Normal] :
    ∃ Φ : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) →* ↥(Work.Higman.omega1 P),
      Function.Bijective Φ ∧
      ∀ a : ↥A, Φ (QuotientGroup.mk a) = ⟨(a : P) ^ 2,
        htop ▸ Work.Higman.pow_mem_powSub (n := 2) a.2⟩ := by
  classical
  -- `A` is abelian, so squaring is multiplicative on `A`.
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  -- The squaring map `A → Ω₁(P)`, which lands in `Ω₁(P) = A²` by the hypothesis `htop`.
  let f : ↥A →* ↥(Work.Higman.omega1 P) :=
    { toFun := fun a => ⟨(a : P) ^ 2, htop ▸ Work.Higman.pow_mem_powSub (n := 2) a.2⟩
      map_one' := by
        refine Subtype.ext ?_
        simp
      map_mul' := fun a b => by
        refine Subtype.ext ?_
        show ((a : P) * (b : P)) ^ 2 = (a : P) ^ 2 * (b : P) ^ 2
        exact Commute.mul_pow (hcomm (a : P) a.2 (b : P) b.2) 2 }
  have hcoe : ∀ a : ↥A, ((f a : ↥(Work.Higman.omega1 P)) : P) = (a : P) ^ 2 := fun a => rfl
  -- The kernel of `f` is exactly `A²` (elements of `A` whose square is `1`).
  have hker : f.ker = (Work.Higman.powSub A 2).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro ha
      have h2 : ((a : P)) ^ 2 = 1 := by
        have hh := congrArg (fun z : ↥(Work.Higman.omega1 P) => (z : P)) ha
        simpa [hcoe] using hh
      exact htop ▸ (h.mem_omega1.mpr h2)
    · intro ha
      refine Subtype.ext ?_
      show ((a : P) ^ 2) = ((1 : ↥(Work.Higman.omega1 P)) : P)
      simp only [Subgroup.coe_one]
      exact h.mem_omega1.mp (htop.symm ▸ ha)
  -- `f` descends to `A / A²`.
  let Φ : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) →* ↥(Work.Higman.omega1 P) :=
    QuotientGroup.lift _ f (le_of_eq hker.symm)
  have hΦ : ∀ a : ↥A, Φ (QuotientGroup.mk a) = f a := fun a =>
    QuotientGroup.lift_mk (N := (Work.Higman.powSub A 2).subgroupOf A) (φ := f)
      (le_of_eq hker.symm) a
  -- `f` is onto: `Ω₁(P) = A²` consists of squares of elements of the abelian group `A`.
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : P) ∈ Work.Higman.powSub A 2 := htop.symm ▸ y.2
    obtain ⟨x, hx, hxsq⟩ := (Work.Higman.mem_powSub_iff (A := A) hcomm).mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by rw [hcoe, hxsq])⟩
  refine ⟨Φ, ⟨?_, ?_⟩, ?_⟩
  · -- injectivity of `Φ`: `Φ x = Φ y` forces `x = y` because `ker Φ = 1`
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [hΦ] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hsq : (a : P) ^ 2 = (b : P) ^ 2 := by
      have hh := congrArg (fun z : ↥(Work.Higman.omega1 P) => (z : P)) hxy
      rwa [hcoe, hcoe] at hh
    have hc : Commute (a : P) (b : P) := hcomm (a : P) a.2 (b : P) b.2
    have hmem : (((a⁻¹ * b : ↥A)) : P) ^ 2 = 1 := by
      show ((a : P)⁻¹ * (b : P)) ^ 2 = 1
      rw [Commute.mul_pow hc.inv_left 2, inv_pow, hsq, inv_mul_cancel]
    exact htop.symm ▸ (h.mem_omega1.mpr hmem)
  · -- surjectivity of `Φ` from that of `f`
    intro y
    obtain ⟨a, ha⟩ := hsurj y
    exact ⟨QuotientGroup.mk a, by rw [hΦ]; exact ha⟩
  · -- the defining formula on representatives
    intro a
    rw [hΦ]
    rfl

end Work.Higman.H8
