import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- The index of the centralizer of a finite normal cyclic subgroup `F` of `D` is bounded by
the number of automorphisms of `F`, which is the Euler totient of `|F|`.

Since `F` is normal, `D` acts on `F` by conjugation, giving a monoid homomorphism
`φ : D →* MulAut F` whose kernel is exactly the centralizer `C_D(F)`. Therefore
`[D : C_D(F)] = |range φ| ≤ |MulAut F| = φ(|F|)`. -/
theorem index_centralizer_le_totient {D : Type} [Group D] [Finite D] (F : Subgroup D) [F.Normal]
    (hFcyc : IsCyclic ↥F) :
    (Subgroup.centralizer (F : Set D)).index ≤ (Nat.card ↥F).totient := by
  let φ : D →* MulAut ↥F := MulAut.conjNormal
  -- The kernel of conjugation on the normal subgroup `F` is the centralizer of `F`.
  have hker : φ.ker = Subgroup.centralizer (F : Set D) := by
    show (MulAut.conjNormal : D →* MulAut ↥F).ker = Subgroup.centralizer (F : Set D)
    ext g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hhF
      have h1 : ((MulAut.conjNormal g) ⟨h, hhF⟩ : ↥F) = ⟨h, hhF⟩ := DFunLike.congr_fun hg _
      have h2 : (g * h * g⁻¹ : D) = h := by
        have := congrArg (fun x : ↥F => (x : D)) h1
        simpa [MulAut.conjNormal_apply] using this
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro hc
      ext h
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hc h h.2]
      group
  rw [← hker, Subgroup.index_ker]
  calc Nat.card φ.range ≤ Nat.card (MulAut ↥F) := Subgroup.card_le_card_group (H := φ.range)
    _ = Nat.totient (Nat.card ↥F) := IsCyclic.card_mulAut (G := ↥F) (h := hFcyc)

end Work.ThmF.ChV12
