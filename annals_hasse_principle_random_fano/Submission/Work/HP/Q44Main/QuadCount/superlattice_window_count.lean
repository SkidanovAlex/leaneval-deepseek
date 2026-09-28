import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.HP.Q44Child.superlattice_count
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.SuperInj
import Submission.Work.HP.MDEstimates.detL_le_prod_lam
import Submission.Work.HP.Lat.detL_ge_one

/-!
# Counting superlattices of a rank-`2` lattice inside a window of successive minima

`Work.HP.Q44Main.QuadCount.superlattice_window_count` bounds the number of primitive rank-`3`
lattices `L ⊇ Λ` whose first three successive minima are bounded by `s 0 ≤ s 1 ≤ s 2`, the lattice
`Λ` being a primitive rank-`2` sublattice of `ℤ^5`:

  `#{L ⊇ Λ : rk L = 3, L primitive, λ_j(L) ≤ s (j-1)} ≤ C (s 0 s 1 s 2)^3`.

The proof has two ingredients.

* *The determinant window.*  By `Work.HP.MDEstimates.detL_le_prod_lam` the covolume of a lattice is
  at most the product of its successive minima, so every `L` in the window satisfies
  `detL L ≤ λ₁(L) λ₂(L) λ₃(L) ≤ s 0 * s 1 * s 2`.  Writing `T = s 0 * s 1 * s 2 / detL Λ` and
  using the hypothesis `detL Λ ≤ s 0 * s 1` together with `1 ≤ s 2`, the window is contained in
  `Q44Child.Sset Λ T = {L ⊇ Λ : rk L = 3, detL L ≤ T * detL Λ}`, and `1 ≤ T`.

* *The superlattice count.*  `Work.HP.Q44Child.superlattice_count` bounds
  `#(Sset Λ T) ≤ C T³ detL Λ`.  Since `detL Λ ≥ 1` (`Work.HP.Lat.detL_ge_one`),
  `T³ detL Λ = (s 0 s 1 s 2)³ / (detL Λ)² ≤ (s 0 s 1 s 2)³`, which is the claimed bound.

The monotonicity of `Set.ncard` along the inclusion requires the *finiteness* of the enclosing set
`Sset Λ T`; this is supplied by the helper `Sset_finite` below, which uses the injective map
`L ↦ ψ(L)` from `Sset Λ T` into the finite set of projected lattice points `uSet Λ T`
(of `Q44Child.SuperInj`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Q44Main.QuadCount

/-- **Finiteness of the determinant window.**  For a primitive rank-`2` lattice `Λ ⊆ ℤ^5` and any
real `T`, only finitely many rank-`3` superlattices `L ⊇ Λ` have `detL L ≤ T * detL Λ`.

This is the finiteness statement underlying `Q44Child.superlattice_count`: the map
`L ↦ ψ(L)` (the generator of the rank-`1` group `π(L) ≤ π(ℤ^5)`) takes values in the finite set
`uSet Λ T` of projected lattice points of norm `≤ T`, and is injective because
`L = {w : ℤ^5 | π(w) ∈ ℤ • ψ(L)}`. -/
theorem Sset_finite (Λ : Submodule ℤ (Fin 5 → ℤ)) (hΛrk : Work.HP.rk Λ = 2)
    (hpr : Work.HP.IsPrimLat Λ) (T : ℝ) :
    (Work.HP.Q44Child.Sset Λ T).Finite := by
  obtain ⟨b, hb, hli, h5⟩ := Work.HP.Q44Child.basis_ext Λ hΛrk hpr
  have hinj : Set.InjOn (Work.HP.Q44Child.psi b Λ hb hli h5 hΛrk hpr T)
      (Work.HP.Q44Child.Sset Λ T) := by
    intro L hL L' hL' heq
    have h1 := (Work.HP.Q44Child.psi_spec hb hli h5 hΛrk hpr hL).2
    have h2 := (Work.HP.Q44Child.psi_spec hb hli h5 hΛrk hpr hL').2
    ext w
    rw [h1 w, h2 w, heq]
  have himg : ((Work.HP.Q44Child.psi b Λ hb hli h5 hΛrk hpr T) ''
      (Work.HP.Q44Child.Sset Λ T)).Finite :=
    (Work.HP.Q44Child.uSet_finite hb hli T).subset (by
      rintro u ⟨L, hL, rfl⟩
      exact (Work.HP.Q44Child.psi_spec hb hli h5 hΛrk hpr hL).1)
  exact Set.Finite.of_finite_image himg hinj

/-- **Counting superlattices in a successive-minima window.**  Uniformly in the primitive rank-`2`
lattice `Λ ⊆ ℤ^5`, the number of primitive rank-`3` lattices `L ⊇ Λ` with
`λ_{j+1}(L) ≤ s j` for `j = 0, 1, 2` is `O((s 0 s 1 s 2)^3)`, provided `1 ≤ s 0 ≤ s 1 ≤ s 2`
and `detL Λ ≤ s 0 * s 1`. -/
theorem superlattice_window_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : Submodule ℤ (Fin 5 → ℤ)) (s : Fin 3 → ℝ),
      Work.HP.rk Λ = 2 → Work.HP.IsPrimLat Λ →
      1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 → Work.HP.detL Λ ≤ s 0 * s 1 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | Λ ≤ L ∧ Work.HP.rk L = 3 ∧ Work.HP.IsPrimLat L ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * (s 0 * s 1 * s 2) ^ 3 := by
  obtain ⟨C, hCpos, hC⟩ := Work.HP.Q44Child.superlattice_count
  refine ⟨C, hCpos, ?_⟩
  intro Λ s hΛrk hΛpr hs0 hs01 hs12 hdet
  -- the determinant threshold of the superlattice count
  set T : ℝ := s 0 * s 1 * s 2 / Work.HP.detL Λ with hT
  have hdetΛ1 : 1 ≤ Work.HP.detL Λ := Work.HP.Lat.detL_ge_one Λ
  have hdetΛpos : 0 < Work.HP.detL Λ := lt_of_lt_of_le zero_lt_one hdetΛ1
  have hs2 : 1 ≤ s 2 := le_trans (le_trans hs0 hs01) hs12
  have hs0s1nn : 0 ≤ s 0 * s 1 := by nlinarith [hs0, hs01]
  -- the superlattice count applies because `T ≥ 1`
  have hT1 : 1 ≤ T := by
    rw [hT, le_div_iff₀ hdetΛpos]
    nlinarith [hdet, hs0s1nn, hs2]
  -- the window sits inside the determinant window `Sset Λ T`
  have hsub : ({L : Submodule ℤ (Fin 5 → ℤ) |
        Λ ≤ L ∧ Work.HP.rk L = 3 ∧ Work.HP.IsPrimLat L ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} : Set (Submodule ℤ (Fin 5 → ℤ)))
      ⊆ Work.HP.Q44Child.Sset Λ T := by
    intro L hL
    obtain ⟨h1, h2, -, h4⟩ := hL
    refine ⟨h1, h2, ?_⟩
    -- `detL L ≤ λ₁(L) λ₂(L) λ₃(L) ≤ s 0 * s 1 * s 2`
    have hprod : (∏ i ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (i + 1))
        = Work.HP.lam L 1 * Work.HP.lam L 2 * Work.HP.lam L 3 := by
      rw [h2]; norm_num [Finset.prod_range_succ]
    have hdetL : Work.HP.detL L ≤ s 0 * s 1 * s 2 := by
      have h := Work.HP.MDEstimates.detL_le_prod_lam L
      rw [hprod] at h
      have h1' : Work.HP.lam L 1 ≤ s 0 := by simpa using h4 0
      have h2' : Work.HP.lam L 2 ≤ s 1 := by simpa using h4 1
      have h3' : Work.HP.lam L 3 ≤ s 2 := by simpa using h4 2
      have hn1 : 0 ≤ Work.HP.lam L 1 := Work.HP.lam_nonneg L 1
      have hn2 : 0 ≤ Work.HP.lam L 2 := Work.HP.lam_nonneg L 2
      have hn3 : 0 ≤ Work.HP.lam L 3 := Work.HP.lam_nonneg L 3
      have hs1nn : 0 ≤ s 1 := le_trans zero_le_one (le_trans hs0 hs01)
      refine h.trans ?_
      have h12 : Work.HP.lam L 1 * Work.HP.lam L 2 ≤ s 0 * s 1 :=
        mul_le_mul h1' h2' hn2 (le_trans hn1 h1')
      exact mul_le_mul h12 h3' hn3 (mul_nonneg (le_trans zero_le_one hs0) hs1nn)
    -- `T * detL Λ = s 0 * s 1 * s 2`
    have hTm : T * Work.HP.detL Λ = s 0 * s 1 * s 2 := by
      rw [hT, div_mul_cancel₀ _ (ne_of_gt hdetΛpos)]
    rw [hTm]
    exact hdetL
  have hfinS : (Work.HP.Q44Child.Sset Λ T).Finite := Sset_finite Λ hΛrk hΛpr T
  have hle : (({L : Submodule ℤ (Fin 5 → ℤ) |
        Λ ≤ L ∧ Work.HP.rk L = 3 ∧ Work.HP.IsPrimLat L ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ ((Work.HP.Q44Child.Sset Λ T).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfinS
  have hC' := hC Λ hΛrk hΛpr T hT1
  -- `T³ detL Λ = (s 0 s 1 s 2)³ / (detL Λ)² ≤ (s 0 s 1 s 2)³` since `detL Λ ≥ 1`
  have hXnn : 0 ≤ s 0 * s 1 * s 2 := by nlinarith [hs0, hs01, hs12]
  have hkey : T ^ 3 * Work.HP.detL Λ ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have heq : T ^ 3 * Work.HP.detL Λ = (s 0 * s 1 * s 2) ^ 3 / (Work.HP.detL Λ) ^ 2 := by
      rw [hT]; field_simp
    rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < (Work.HP.detL Λ) ^ 2)]
    exact le_mul_of_one_le_right (pow_nonneg hXnn 3)
      (by simpa using pow_le_pow_left₀ zero_le_one hdetΛ1 2)
  calc (({L : Submodule ℤ (Fin 5 → ℤ) |
        Λ ≤ L ∧ Work.HP.rk L = 3 ∧ Work.HP.IsPrimLat L ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ ((Work.HP.Q44Child.Sset Λ T).ncard : ℝ) := hle
    _ ≤ C * T ^ 3 * Work.HP.detL Λ := hC'
    _ = C * (T ^ 3 * Work.HP.detL Λ) := by ring
    _ ≤ C * (s 0 * s 1 * s 2) ^ 3 := mul_le_mul_of_nonneg_left hkey hCpos.le

end Work.HP.Q44Main.QuadCount
