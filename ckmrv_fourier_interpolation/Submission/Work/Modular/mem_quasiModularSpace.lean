import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The function `0 : ℍ → ℂ` is quasimodular of depth at most `d` and weight `k`. -/
theorem IsQuasiModularFormDepth.zero (d : ℕ) (k : ℤ) :
    IsQuasiModularFormDepth d k (0 : ℍ → ℂ) :=
  ⟨0, by simp⟩

/-- Quasimodularity of fixed weight and depth is preserved by addition. -/
theorem IsQuasiModularFormDepth.add {d : ℕ} {k : ℤ} {f g : ℍ → ℂ}
    (hf : IsQuasiModularFormDepth d k f) (hg : IsQuasiModularFormDepth d k g) :
    IsQuasiModularFormDepth d k (f + g) := by
  obtain ⟨mf, rfl⟩ := hf
  obtain ⟨mg, rfl⟩ := hg
  refine ⟨fun j => mf j + mg j, ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_add]

/-- Quasimodularity of fixed weight and depth is preserved by `ℂ`-scalar multiplication. -/
theorem IsQuasiModularFormDepth.smul {d : ℕ} {k : ℤ} {f : ℍ → ℂ} (c : ℂ)
    (hf : IsQuasiModularFormDepth d k f) :
    IsQuasiModularFormDepth d k (c • f) := by
  obtain ⟨mf, rfl⟩ := hf
  refine ⟨fun j => c • mf j, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext τ
  simp only [Pi.smul_apply, FunLike.coe_smul, Pi.mul_apply]
  ring

theorem mem_quasiModularSpace {d : ℕ} {k : ℤ} {f : ℍ → ℂ} :
    f ∈ quasiModularSpace d k ↔ IsQuasiModularFormDepth d k f := by
  constructor
  · intro hf
    exact Submodule.span_induction (p := fun x _ => IsQuasiModularFormDepth d k x)
      (fun _ hx => hx) (IsQuasiModularFormDepth.zero d k)
      (fun _ _ _ _ hx hy => hx.add hy) (fun c _ _ hx => hx.smul c) hf
  · intro hf
    exact Submodule.subset_span hf

end Work.Modular
