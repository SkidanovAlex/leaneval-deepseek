import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Module

namespace NK.LocalCFT.Units.EllRank

/-- Arithmetic: if `n * e = m * e + j` with `0 < e` and `j < e`, then `n = m`.
Division by `e` reads off the quotient. -/
lemma eq_of_mul_eq_mul_add {n m e j : ℕ} (he : 0 < e) (hj : j < e)
    (h : n * e = m * e + j) : n = m := by
  have h1 : (m * e + j) / e = m := by
    have hm : m * e + j = j + e * m := by ring
    rw [hm, Nat.add_mul_div_left j m he, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : n * e / e = n := by
    rw [Nat.mul_comm n e, Nat.mul_div_right n he]
  rw [h] at h2
  rw [h2] at h1
  exact h1

/-- Over the field `𝔽_p`, an infinite-dimensional vector space has infinitely many
subspaces of codimension `e` (i.e. with quotient of cardinality `p ^ e`), for every
`e ≥ 1`.

The construction: fix a basis of `V`, let `g : ℕ ↪ ι` be an injection into the basis
index set (possible since `V` is infinite-dimensional), and for each `n : ℕ` take the
kernel of the projection to the `e` coordinates `g (n * e), …, g (n * e + e - 1)`.
Distinct blocks of coordinates give distinct kernels. -/
theorem infinite_codim_submodule {p e : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (he : 1 ≤ e) (hV : ¬ FiniteDimensional (ZMod p) V) :
    Infinite {W : Submodule (ZMod p) V // Nat.card (V ⧸ W) = p ^ e} := by
  have hι : Infinite (Module.Free.ChooseBasisIndex (ZMod p) V) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Finite (Module.Free.ChooseBasisIndex (ZMod p) V) := hfin
    exact hV (Module.Basis.finiteDimensional_of_finite (Module.Free.chooseBasis (ZMod p) V))
  haveI := hι
  let b : Basis (Module.Free.ChooseBasisIndex (ZMod p) V) (ZMod p) V :=
    Module.Free.chooseBasis (ZMod p) V
  let g : ℕ ↪ Module.Free.ChooseBasisIndex (ZMod p) V := Infinite.natEmbedding _
  let F : ℕ → V →ₗ[ZMod p] (Fin e → ZMod p) := fun n =>
    LinearMap.pi (fun j : Fin e => (Finsupp.lapply (g (n * e + (j : ℕ)))).comp
      (b.repr : V →ₗ[ZMod p] (Module.Free.ChooseBasisIndex (ZMod p) V →₀ ZMod p)))
  have hepos : 0 < e := he
  let j0 : Fin e := ⟨0, hepos⟩
  -- value of `F k` on the basis vector `b (g (n * e))`
  have hFval : ∀ (k n : ℕ) (j : Fin e),
      (F k (b (g (n * e)))) j = if n * e = k * e + (j : ℕ) then 1 else 0 := by
    intro k n j
    simp only [F, LinearMap.pi_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
      Basis.repr_self, LinearEquiv.coe_coe, Finsupp.single_apply]
    simp only [g.injective.eq_iff]
  -- each `F n` is surjective
  have hsurj : ∀ n, Function.Surjective (F n) := by
    intro n y
    refine ⟨∑ j : Fin e, y j • b (g (n * e + (j : ℕ))), ?_⟩
    funext j
    simp only [F, LinearMap.pi_apply, LinearMap.comp_apply, Finsupp.lapply_apply]
    simp only [map_sum, map_smul, Basis.repr_self, LinearEquiv.coe_coe]
    rw [Finset.sum_apply']
    simp only [Finsupp.smul_apply, Finsupp.single_apply, g.injective.eq_iff,
      Nat.add_left_cancel_iff, Fin.val_inj, smul_ite, smul_one, smul_zero]
    rw [Finset.sum_ite_eq']
    simp
  -- so the kernel has quotient of cardinality `p ^ e`
  have hcard : ∀ n, Nat.card (V ⧸ (F n).ker) = p ^ e := by
    intro n
    rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective (F n) (hsurj n)).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  -- distinct `n` give distinct kernels
  have hker : ∀ n m, n ≠ m → (F n).ker ≠ (F m).ker := by
    intro n m hnm hEq
    have hnonzero : F n (b (g (n * e))) ≠ 0 := by
      intro h0
      have h1 : (F n (b (g (n * e)))) j0 = 1 := by
        have hj0 : (j0 : ℕ) = 0 := rfl
        rw [hFval n n j0, hj0, Nat.add_zero, if_pos rfl]
      rw [h0] at h1
      simp at h1
    have hzero : F m (b (g (n * e))) = 0 := by
      funext j
      rw [hFval m n j]
      rw [if_neg (fun hcon => hnm (eq_of_mul_eq_mul_add hepos j.isLt hcon))]
      rfl
    have : b (g (n * e)) ∈ (F n).ker := by
      rw [hEq, LinearMap.mem_ker]
      exact hzero
    exact hnonzero (LinearMap.mem_ker.mp this)
  refine Infinite.of_injective
    (fun n => (⟨(F n).ker, hcard n⟩ :
      {W : Submodule (ZMod p) V // Nat.card (V ⧸ W) = p ^ e})) ?_
  intro n m hnm
  have hkm : (F n).ker = (F m).ker := congrArg Subtype.val hnm
  by_contra h
  exact hker n m h hkm

end NK.LocalCFT.Units.EllRank
