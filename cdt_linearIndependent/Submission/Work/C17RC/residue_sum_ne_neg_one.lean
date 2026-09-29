import Mathlib
import Submission.Work.C17RC.defs

namespace Work.C17RC

/-- **A sum of residues each equal to `1` or `2` is never `-1`.**  If `B` is monic with pairwise
distinct roots, `deg A < deg B`, the top coefficient `A.coeff (deg B - 1)` is `-1`, and every
residue `A(β)/B'(β)` at a root `β` of `B` equals `1` or `2`, then we get a contradiction: the
Lagrange/residue identity `∑_{β ∈ B.roots} A(β)/B'(β) = A.coeff (deg B - 1)`
(`Work.C17.roots_sum_div_derivative`) exhibits `-1` as a sum of complex numbers whose real parts
are all in `{1,2}`, whence the real part of that sum is `≥ 0`. -/
theorem residue_sum_ne_neg_one (A B : Polynomial ℂ) (hB : B.Monic) (hnodup : B.roots.Nodup)
    (hdeg : A.natDegree < B.natDegree) (hlc : A.coeff (B.natDegree - 1) = -1)
    (hres : ∀ β ∈ B.roots, A.eval β / B.derivative.eval β = 1 ∨ A.eval β / B.derivative.eval β = 2) :
    False := by
  classical
  set c : ℂ → ℂ := fun β => A.eval β / B.derivative.eval β with hcdef
  -- Step 1: the Lagrange/residue identity says the sum of the residues is the top coefficient.
  have hsum := Work.C17.roots_sum_div_derivative A B hB hnodup hdeg
  have hsumc : (B.roots.map c).sum = -1 := by
    rw [hcdef, hsum, hlc]
  -- Step 2: each residue is `1` or `2`, so its real part is nonnegative.
  have hc : ∀ β ∈ B.roots, c β = 1 ∨ c β = 2 := by
    intro β hβ
    rw [hcdef]
    exact hres β hβ
  have hre : ((B.roots.map c).sum).re = ((B.roots.map c).map Complex.re).sum :=
    map_multiset_sum Complex.reAddGroupHom _
  have hnonneg : 0 ≤ ((B.roots.map c).map Complex.re).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hy
    rcases hc β hβ with h | h <;> simp [h]
  -- Step 3: but the real part of the sum is the real part of `-1`.
  have hone : ((B.roots.map c).map Complex.re).sum = -1 := by
    rw [← hre, hsumc]
    norm_num
  linarith

end Work.C17RC
