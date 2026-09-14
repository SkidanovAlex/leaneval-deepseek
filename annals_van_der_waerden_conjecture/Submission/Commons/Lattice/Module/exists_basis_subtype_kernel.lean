import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Lattice.Module.basis_extension_pure_rank
import Submission.Commons.LinearAlgebra.Matrix.finrank_range_mulVecLin_eq

open Module Submodule
open scoped BigOperators

noncomputable section

namespace Commons.Lattice.Module

/-- **Adapted basis for the integer kernel of a full-row-rank matrix.** Let `b : Fin n → Fin N → ℤ` be the rows of an `n × N` integer matrix whose rows are linearly independent over `ℚ` (with `n < N`). Then there is a `ℤ`-basis `e` of `ℤ^N` (i.e. of `Fin N → ℤ`) such that the integer kernel `{x | ∀ l, ∑ k, b l k * x k = 0}` is exactly the `ℤ`-span of the first `N - n` basis vectors `e (Fin.castLE (Nat.sub_le N n) j)`.

Proof route. Put `M := (Fin N → ℤ)`, `B := Matrix.of b`, `Λ := (B.mulVecLin).ker`. The kernel `Λ` is pure in `M` (`a • x ∈ Λ` with `a ≠ 0` implies `x ∈ Λ`, since `Fin n → ℤ` is torsion-free). By `Commons.Lattice.Module.basis_extension_pure_rank` it suffices to have a `ℤ`-basis `bN : Basis (Fin n₀) ℤ Λ` with `n₀ = N - n`; then the extension result produces `e` with `e (Fin.castLE h j) = bN j` for `j < n₀`, and the kernel is the span of those (both inclusions are immediate). The rank computation `n₀ = N - n`: the `ℤ`-rank-nullity `Submodule.finrank_quotient_add_finrank` plus `LinearMap.quotKerEquivRange` give `finrank ℤ Λ = N - finrank ℤ (range B.mulVecLin)`; for `finrank ℤ (range B.mulVecLin) = n` one can use the independent result `Commons.LinearAlgebra.Matrix.finrank_range_mulVecLin_eq` once it exists, or redo it directly (a nonzero maximal minor plus Cramer's rule gives `d • ℤ^n ⊆ range B.mulVecLin` for a nonzero integer `d`). -/
theorem exists_basis_subtype_kernel {n N : ℕ} (hn : n < N) (b : Fin n → Fin N → ℤ)
    (hli : LinearIndependent ℚ (fun l : Fin n => fun k : Fin N => ((b l k : ℤ) : ℚ))) :
    ∃ e : Module.Basis (Fin N) ℤ (Fin N → ℤ),
      ∀ x : Fin N → ℤ, (∀ l, ∑ k, b l k * x k = 0) ↔
        ∃ a : Fin (N - n) → ℤ, x = ∑ j, a j • e (Fin.castLE (Nat.sub_le N n) j) := by
  classical
  set B : Matrix (Fin n) (Fin N) ℤ := Matrix.of b with hB
  set Λ : Submodule ℤ (Fin N → ℤ) := LinearMap.ker B.mulVecLin with hΛ
  have hBx : ∀ x : Fin N → ℤ, B.mulVecLin x = fun l => ∑ k, b l k * x k := by
    intro x
    ext l
    simp [hB, Matrix.mulVec_apply, dotProduct]
  have hker : ∀ x : Fin N → ℤ, x ∈ Λ ↔ ∀ l, ∑ k, b l k * x k = 0 := by
    intro x
    rw [hΛ, LinearMap.mem_ker, hBx x, funext_iff]
    simp
  have hfin_range : Module.finrank ℤ (LinearMap.range B.mulVecLin) = n := by
    refine Commons.LinearAlgebra.Matrix.finrank_range_mulVecLin_eq B ?_
    rw [hB]
    exact hli
  have hfinΛ : Module.finrank ℤ Λ = N - n := by
    have hquot : Module.finrank ℤ ((Fin N → ℤ) ⧸ Λ) =
        Module.finrank ℤ (LinearMap.range B.mulVecLin) :=
      LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange B.mulVecLin)
    have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := Fin N → ℤ) Λ
    rw [hquot, hfin_range, Module.finrank_fin_fun ℤ] at hrn
    omega
  let bN : Module.Basis (Fin (N - n)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hfinΛ
  have hpure : ∀ x : Fin N → ℤ, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ Λ) → x ∈ Λ := by
    rintro x ⟨a, ha, hax⟩
    rw [hker] at hax ⊢
    intro l
    have hkey : a * (∑ k, b l k * x k) = 0 := by
      rw [Finset.mul_sum, ← hax l]
      exact Finset.sum_congr rfl (fun k _ => by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring)
    exact (mul_eq_zero.mp hkey).resolve_left ha
  obtain ⟨e, he⟩ := Commons.Lattice.Module.basis_extension_pure_rank (M := Fin N → ℤ)
    (m := N) (d := N - n) (Nat.sub_le N n) Λ (Pi.basisFun ℤ (Fin N)) bN hpure
  have hspanΛ : Submodule.span ℤ
      (Set.range (fun j : Fin (N - n) => ((bN j : Λ) : Fin N → ℤ))) = Λ := by
    have hrange : Set.range (fun j : Fin (N - n) => ((bN j : Λ) : Fin N → ℤ)) =
        Λ.subtype '' Set.range bN := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨bN j, ⟨j, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
    rw [hrange, ← Submodule.map_span, bN.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : Submodule.span ℤ
      (Set.range (fun j : Fin (N - n) => e (Fin.castLE (Nat.sub_le N n) j))) = Λ := by
    have hfun : (fun j : Fin (N - n) => e (Fin.castLE (Nat.sub_le N n) j)) =
        (fun j : Fin (N - n) => ((bN j : Λ) : Fin N → ℤ)) := funext he
    rw [hfun, hspanΛ]
  refine ⟨e, fun x => ?_⟩
  rw [← hker x]
  constructor
  · intro hx
    have hxspan : x ∈ Submodule.span ℤ
        (Set.range (fun j : Fin (N - n) => e (Fin.castLE (Nat.sub_le N n) j))) := by
      rw [hspan]
      exact hx
    rcases (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxspan with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨a, rfl⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun ℤ]
    exact ⟨a, rfl⟩

end Commons.Lattice.Module