import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

/-- The coordinate hyperplane `{x : 𝔽₂ⁿ⁺¹ | x 0 = 0}` is the kernel of the projection onto
the `0`-th coordinate; its dimension is `n`.

Proof: the projection `f` is surjective, so `finrank f.range = finrank 𝔽₂ = 1`, and the
rank-nullity theorem `finrank f.range + finrank f.ker = finrank 𝔽₂ⁿ⁺¹ = n + 1` gives
`finrank (ker f) = n`. -/
lemma finrank_ker_proj_coord (n : ℕ) :
    Module.finrank (ZMod 2)
      (LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin (n + 1) => ZMod 2)
        (0 : Fin (n + 1)))) = n := by
  classical
  let f : (Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin (n + 1) => ZMod 2) (0 : Fin (n + 1))
  change Module.finrank (ZMod 2) ↥(LinearMap.ker f) = n
  have hfr := LinearMap.finrank_range_add_finrank_ker f
  have hrange : f.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨Pi.single 0 y, by simp [f, LinearMap.proj_apply]⟩
  have h1 : Module.finrank (ZMod 2) ↥f.range = 1 := by
    rw [hrange, finrank_top]
    exact finrank_self (ZMod 2)
  have h2 : Module.finrank (ZMod 2) (Fin (n + 1) → ZMod 2) = n + 1 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  rw [h1, h2] at hfr
  omega

/-- There are no `r`-dimensional subspaces of a finite-dimensional space `V` when
`r > finrank V`.  (The count is phrased with `Nat.card`; this is the "empty type" case.) -/
lemma natCard_submodule_finrank_eq_zero_of_lt {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {r : ℕ} (h : Module.finrank K V < r) :
    Nat.card {W : Submodule K V // Module.finrank K W = r} = 0 := by
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun W => by
    have hle := Submodule.finrank_le W.1
    omega⟩

/-- **Pascal's identity for the Gaussian binomial `[n choose m]_2`**: the number of
`(m+1)`-dimensional subspaces of `𝔽₂ⁿ⁺¹` is the number in `𝔽₂ⁿ` (those contained in a
fixed hyperplane `𝔽₂ⁿ ⊂ 𝔽₂ⁿ⁺¹`) plus `2^(n-m)` times the number of `m`-dimensional
subspaces of `𝔽₂ⁿ` (those not contained in the hyperplane, which are the graphs of linear
maps `𝔽₂ⁿ → 𝔽₂ⁿ / (m-dim subspace)`).

Suggested proof: split the `(m+1)`-subspaces of `𝔽₂ⁿ⁺¹` according to whether they are
contained in the coordinate hyperplane `H := {x | x 0 = 0}` (identified with `𝔽₂ⁿ`); the
count of the latter is `2^(n-m) * [n choose m]_2` by the fibre computation in
`Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq`
(with `L := H`, `ℓ₀ := m+1`, `j := m`). -/
theorem card_submodule_pascal_zmod_two (n m : ℕ) :
    Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
        Module.finrank (ZMod 2) W = m + 1} =
      Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
          Module.finrank (ZMod 2) W = m + 1} +
        2 ^ (n - m) * Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
          Module.finrank (ZMod 2) W = m} := by
  classical
  have hV : Module.finrank (ZMod 2) (Fin (n + 1) → ZMod 2) = n + 1 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hVn : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
    rw [Module.finrank_pi, Fintype.card_fin]
  by_cases hmn : m ≤ n
  · -- main case: `m ≤ n`, split the `(m+1)`-subspaces into those inside `H` and those not
    let H : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) :=
      LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin (n + 1) => ZMod 2)
        (0 : Fin (n + 1)))
    have hH : Module.finrank (ZMod 2) H = n := finrank_ker_proj_coord n
    -- the subspaces contained in `H`
    have hInH : Nat.card {x : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
          x ≤ H ∧ Module.finrank (ZMod 2) x = m + 1} =
        Nat.card {u : Submodule (ZMod 2) ↥H // Module.finrank (ZMod 2) u = m + 1} :=
      card_submodule_le_finrank_eq H (m + 1)
    have hswap : Nat.card {x : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
          Module.finrank (ZMod 2) x = m + 1 ∧ x ≤ H} =
        Nat.card {x : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
          x ≤ H ∧ Module.finrank (ZMod 2) x = m + 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun x => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩))
    have hTransport : Nat.card {u : Submodule (ZMod 2) ↥H //
          Module.finrank (ZMod 2) u = m + 1} =
        Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
          Module.finrank (ZMod 2) W = m + 1} :=
      card_submodule_finrank_eq_of_finrank_eq (K := ZMod 2) (V := ↥H)
        (V' := Fin n → ZMod 2) (by rw [hH, hVn]) (ℓ := m + 1)
    have hIn := hswap.trans (hInH.trans hTransport)
    -- the subspaces not contained in `H`
    have hOut : Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
          Module.finrank (ZMod 2) W = m + 1 ∧ ¬ W ≤ H} =
        2 ^ (n - m) * Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
          Module.finrank (ZMod 2) W = m} := by
      -- a `(m+1)`-dimensional `W` is *not* contained in `H` iff `W ⊓ H` is `m`-dimensional
      have hiff : ∀ W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2),
          (Module.finrank (ZMod 2) W = m + 1 ∧ ¬ W ≤ H) ↔
          (Module.finrank (ZMod 2) W = m + 1 ∧ Module.finrank (ZMod 2) ↥(H ⊓ W) = m) := by
        intro W
        constructor
        · rintro ⟨hW, hnotle⟩
          have hlt : H < H ⊔ W :=
            lt_of_le_of_ne le_sup_left (fun h => hnotle (h ▸ le_sup_right))
          have hsupfin : Module.finrank (ZMod 2) ↥(H ⊔ W) = n + 1 := by
            have hltfin := Submodule.finrank_lt_finrank_of_lt hlt
            have hle := Submodule.finrank_le (H ⊔ W)
            rw [hH] at hltfin
            rw [hV] at hle
            omega
          have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq H W
          rw [hsupfin, hH, hW] at hsupinf
          omega
        · rintro ⟨hW, hinf⟩
          refine ⟨hW, fun hle => ?_⟩
          have hinf' : H ⊓ W = W := inf_eq_right.mpr hle
          rw [hinf'] at hinf
          omega
      have hcount := card_submodule_finrank_inf_eq (V := Fin (n + 1) → ZMod 2) H n (m + 1) m
        hH hmn (by omega) (by rw [hV]; omega)
      -- the remaining factor is the number of `1`-dimensional subspaces of `𝔽₂¹`, i.e. `1`
      have hG : Nat.card {W : Submodule (ZMod 2)
            (Fin (Module.finrank (ZMod 2) (Fin (n + 1) → ZMod 2) - n) → ZMod 2) //
            Module.finrank (ZMod 2) W = m + 1 - m} = 1 := by
        rw [hV, show n + 1 - n = 1 from by omega, show m + 1 - m = 1 from by omega]
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨⊤, by rw [finrank_top, Module.finrank_pi, Fintype.card_fin]⟩,
          fun y => Subtype.ext ?_⟩
        exact Submodule.eq_top_of_finrank_eq
          (by rw [y.2, Module.finrank_pi, Fintype.card_fin])
      calc Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
              Module.finrank (ZMod 2) W = m + 1 ∧ ¬ W ≤ H}
          = Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
              Module.finrank (ZMod 2) W = m + 1 ∧ Module.finrank (ZMod 2) ↥(H ⊓ W) = m} :=
            Nat.card_congr (Equiv.subtypeEquivRight hiff)
        _ = 2 ^ (n - m) * Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
              Module.finrank (ZMod 2) W = m} := by
            rw [hcount, hG, mul_one, show m + 1 - m = 1 from by omega, mul_one]
    -- split all `(m+1)`-subspaces of `𝔽₂ⁿ⁺¹` according to `W ≤ H`
    have hsplit : Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
          Module.finrank (ZMod 2) W = m + 1} =
        Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
            Module.finrank (ZMod 2) W = m + 1 ∧ W ≤ H} +
          Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
            Module.finrank (ZMod 2) W = m + 1 ∧ ¬ W ≤ H} := by
      let e : {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
            Module.finrank (ZMod 2) W = m + 1} ≃
          ({W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
              Module.finrank (ZMod 2) W = m + 1 ∧ W ≤ H} ⊕
            {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
              Module.finrank (ZMod 2) W = m + 1 ∧ ¬ W ≤ H}) :=
        (Equiv.sumCompl (fun x : {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
              Module.finrank (ZMod 2) W = m + 1} => x.1 ≤ H)).symm.trans
          (Equiv.sumCongr
            (Equiv.subtypeSubtypeEquivSubtypeInter
              (p := fun W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) =>
                Module.finrank (ZMod 2) W = m + 1)
              (q := fun W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) => W ≤ H))
            (Equiv.subtypeSubtypeEquivSubtypeInter
              (p := fun W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) =>
                Module.finrank (ZMod 2) W = m + 1)
              (q := fun W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) => ¬ W ≤ H)))
      calc Nat.card {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
              Module.finrank (ZMod 2) W = m + 1}
          = Nat.card ({W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
                Module.finrank (ZMod 2) W = m + 1 ∧ W ≤ H} ⊕
              {W : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
                Module.finrank (ZMod 2) W = m + 1 ∧ ¬ W ≤ H}) := Nat.card_congr e
        _ = _ := Nat.card_sum
    rw [hsplit, hIn, hOut]
  · -- degenerate case: `m > n`, everything is empty
    have hnm : n < m := by omega
    rw [natCard_submodule_finrank_eq_zero_of_lt (V := Fin (n + 1) → ZMod 2) (r := m + 1)
          (by rw [hV]; omega),
      natCard_submodule_finrank_eq_zero_of_lt (V := Fin n → ZMod 2) (r := m + 1)
          (by rw [hVn]; omega),
      natCard_submodule_finrank_eq_zero_of_lt (V := Fin n → ZMod 2) (r := m)
          (by rw [hVn]; omega)]
    simp

end

end Commons.LinearAlgebra.Submodule
