import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDDefs

open Work.SSGRoute

theorem toClass_apply_congr (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup)
    {f g : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H)
    (h : Work.SSGRoute.toClass p k Ω K (ZMod p) H f = Work.SSGRoute.toClass p k Ω K (ZMod p) H g) :
    ∀ σ ∈ H, f σ = g σ := by
  intro σ hσ
  -- Step 1: unwrap `toClass` on both sides, using the cocycle hypotheses.
  have hq : (Submodule.mkQ (R := ZMod p) (Submodule.comap (lcCocycles p k Ω K (ZMod p) H).subtype
        (coboundaries p k Ω K (ZMod p) H)) ⟨f, hf⟩ : H1loc p k Ω K (ZMod p) H)
      = Submodule.mkQ (R := ZMod p) (Submodule.comap (lcCocycles p k Ω K (ZMod p) H).subtype
        (coboundaries p k Ω K (ZMod p) H)) ⟨g, hg⟩ := by
    simpa only [toClass, dif_pos hf, dif_pos hg] using h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hq
  -- Step 2: equality in the quotient means the difference is a coboundary.
  have hmem : (f - g) ∈ coboundaries p k Ω K (ZMod p) H := by
    have h1 := (Submodule.Quotient.eq _).mp hq
    have h2 := Submodule.mem_comap.mp h1
    simpa using h2
  obtain ⟨m, hm⟩ := hmem
  -- Step 3: elements of `H ≤ K.fixingSubgroup` restrict to `1` in `Gal(K/k)`, so the
  -- coboundary `σ ↦ res σ • m - m` vanishes on `H`.
  have hres : SSGRoute.res k K σ = 1 := by
    have hk : σ ∈ (SSGRoute.res k K).ker := by
      rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
        IntermediateField.restrictNormalHom_ker (E := K)]
      exact hH hσ
    exact MonoidHom.mem_ker.mp hk
  have hzero : (f - g) σ = 0 := by
    rw [hm σ hσ, hres, one_smul, sub_self]
  have : f σ - g σ = 0 := by simpa using hzero
  exact sub_eq_zero.mp this

end Work.SSGRoute.LTDDefs
