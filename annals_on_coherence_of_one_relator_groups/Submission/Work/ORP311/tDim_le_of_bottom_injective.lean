/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (node P5 of the Følner/Lück argument for JZLA20 Proposition 3.11)

# The window dimension bound `tDim n (sWin t m) V ≤ n`

This file proves node P5 of the Følner/Lück approximation argument for [JZLA20, Proposition 3.11]
(Jaikin-Zapirain--López-Álvarez, arXiv:1810.12135; the analytic core, Jaikin's survey Theorem 12.1
/ Corollary 12.2).

Let `N ⊴ ⟨N, t⟩` with `t` of infinite order modulo `N` (`Work.ORP311.P311.TwistData N t`) and let
`X_m = ⋃_{|j| ≤ m} N t^j` be the `m`-th Følner window.  For a closed subspace
`V ≤ ℓ²(X_m)ⁿ` which is invariant under the right `N`-action and *injective under the bottom
block projection* `blk (-m)`, the transversal dimension on the transversal
`sWin t m = {t^j | |j| ≤ m}` is bounded by `n`:

  `tDim n (sWin t m) V ≤ n`.

## Strategy

The window `X_m` is a disjoint union of the `2m+1` cosets `N t^j`, `|j| ≤ m`, and these cosets are
permuted by the right regular action.  Transporting `V` along the isometry

  `winIso : ⊕_{c : Fin (n(2m+1))} ℓ²(N) →ₗᵢ[ℂ] ⊕_{i : Fin n} ℓ²(G)`

which spreads the `c`-th copy of `ℓ²(N)` onto the `c`-th coset of the window
(`Submission.Work.ORP311.lp_extend_isometry`), one obtains a `diagOp`-invariant subspace `V'` of
`ℓ²(N)^{n(2m+1)}`, with `hdim V' = tDim n (sWin t m) V` (`starProjection_comap_isometry` plus the
reindexing of the coordinates).

The dimension bound then follows from the "one bounded certificate" principle: injectivity of
`blk (-m)` on `V` says exactly that the projection of `V'` to the `n` coordinates of the *bottom*
coset `N t^{-m}` is injective, and an injective equivariant map can only lower the dimension
(`Work.ORP311.hdim_le_hdim_range_of_injective`), while the bottom coordinates span only `n`
dimensions.

## Main definitions

* `Work.ORP311.winDim`, `Work.ORP311.winDecode`, `Work.ORP311.winExp` — the bookkeeping of the
  `n(2m+1)` coordinates of the window decomposition;
* `Work.ORP311.winIdx` — the injection `↥N × Fin (n(2m+1)) → G × Fin n` underlying `winIso`;
* `Work.ORP311.winIso` — the window isometry.

## Main result

* `Work.ORP311.tDim_le_of_bottom_injective` — the bound `tDim n (sWin t m) V ≤ n`.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.HdimInject
import Submission.Work.ORP311.tDim_ell2Sub_of_subset
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.starProjection_comap_isometry
import Submission.Work.ORP311.lp_extend_isometry
import Submission.Work.ORP311.card_sWin
import Submission.Work.ORP311.coset_subset_window
import Submission.Work.ORP311.mem_ell2Sub_iff
import Submission.Work.ORP311.Ell2SubAux
import Submission.Work.ORP311.ell2Sub_mono
import Submission.Work.ORP311.FolnerWindow
import Submission.Work.ORVonNeumann.Rep.vnHdimMono
import Submission.Work.ORP311.hdim_le_card_of_orthogonal_delta

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct Classical

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ### The bookkeeping of the window coordinates -/

/-- The number `n * (2m+1)` of `ℓ²(N)`-copies in the window decomposition of `ℓ²(X_m)ⁿ`:
`2m+1` cosets, each carrying `n` coordinates. -/
abbrev winDim (n m : ℕ) : ℕ := n * (2 * m + 1)

/-- The indexing `Fin (n(2m+1)) ≃ Fin (2m+1) × Fin n` of the window coordinates: the first
component is the coset index `j ∈ [-m, m]`, written as `j + m : Fin (2m+1)`, the second the
`ℓ²(G)`-coordinate. -/
noncomputable def winDecode (n m : ℕ) : Fin (winDim n m) ≃ Fin (2 * m + 1) × Fin n :=
  (finProdFinEquiv (m := n) (n := 2 * m + 1)).symm.trans
    (Equiv.prodComm (Fin n) (Fin (2 * m + 1)))

/-- The exponent `j - m ∈ [-m, m]` attached to `j : Fin (2m+1)`. -/
def winExp (m : ℕ) (j : Fin (2 * m + 1)) : ℤ := (j : ℤ) - (m : ℤ)

theorem winExp_mem (m : ℕ) (j : Fin (2 * m + 1)) :
    -((m : ℤ)) ≤ winExp m j ∧ winExp m j ≤ (m : ℤ) := by
  have hj : (j : ℕ) < 2 * m + 1 := j.isLt
  constructor <;> simp only [winExp] <;> omega

theorem winExp_injective (m : ℕ) : Function.Injective (winExp m) := by
  intro a b hab
  simp only [winExp] at hab
  have h : (a : ℤ) = (b : ℤ) := by omega
  exact Fin.ext (by omega)

theorem winExp_eq_zero {m : ℕ} {j : Fin (2 * m + 1)} :
    winExp m j = 0 ↔ (j : ℕ) = m := by
  simp only [winExp]
  omega

/-- **The index map of the window decomposition.**  It sends the `ℓ²(N)`-coordinate
`(k, c)` to the `ℓ²(G)`-coordinate `(t^{j(c)} · k, i(c))`, where `(j(c), i(c)) = winDecode c`.
Its image is the set of coordinates concentrated on the window `X_m`. -/
noncomputable def winIdx (N : Subgroup G) (t : G) (n m : ℕ) :
    (↥N × Fin (winDim n m)) → G × Fin n :=
  fun p => (t ^ winExp m (winDecode n m p.2).1 * (p.1 : G), (winDecode n m p.2).2)

variable {N : Subgroup G} {t : G}

/-- **The index map `winIdx` is injective**, by uniqueness of the decomposition
`g = t^j · n` (`j ∈ [-m,m]`, `n ∈ N`) coming from `TwistData.inf`. -/
theorem winIdx_injective (h : P311.TwistData N t) (n m : ℕ) :
    Function.Injective (winIdx N t n m) := by
  rintro ⟨k, c⟩ ⟨k', c'⟩ he
  simp only [winIdx, Prod.mk.injEq] at he
  obtain ⟨he1, he2⟩ := he
  -- the exponents agree, because `t ^ (e - e') = k' * k⁻¹ ∈ N`
  have hexp : winExp m (winDecode n m c).1 = winExp m (winDecode n m c').1 := by
    have hmem : t ^ (winExp m (winDecode n m c).1 - winExp m (winDecode n m c').1) ∈ N := by
      have h2 : t ^ (winExp m (winDecode n m c).1 - winExp m (winDecode n m c').1)
          = (k' : G) * (k : G)⁻¹ := by
        have h3 : t ^ (-winExp m (winDecode n m c').1)
            * (t ^ winExp m (winDecode n m c).1 * (k : G)) = (k' : G) := by
          rw [he1, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
        have h4 : t ^ (winExp m (winDecode n m c).1 - winExp m (winDecode n m c').1)
            * (k : G) = (k' : G) := by
          rw [← mul_assoc, ← zpow_add] at h3
          have hz : -winExp m (winDecode n m c').1 + winExp m (winDecode n m c).1
              = winExp m (winDecode n m c).1 - winExp m (winDecode n m c').1 := by ring
          rwa [hz] at h3
        have h5 := congrArg (fun x : G => x * (k : G)⁻¹) h4
        simpa [mul_assoc] using h5
      rw [h2]
      exact N.mul_mem k'.2 (N.inv_mem k.2)
    exact sub_eq_zero.mp (h.inf _ hmem)
  have hc : c = c' := by
    apply (winDecode n m).injective
    exact Prod.ext (winExp_injective m hexp) he2
  subst hc
  have hk : k = k' := Subtype.ext (mul_left_cancel he1)
  subst hk
  rfl

/-! ### The window isometry -/

/-- **The window isometry.**  It spreads the `c`-th copy of `ℓ²(N)` (a coordinate of
`HSum (G := ↥N) (n(2m+1))`) onto the coset `N t^{j(c)}` of the window, in the `i(c)`-th
`ℓ²(G)`-coordinate: on basis vectors

  `winIso (hinclude c (δ_k)) = hinclude (i c) (δ_{t^{j(c)} · k})`.

It is the composite of the reindexing `HilbertBasis.repr` of both sides with the "extend by zero
along an injection" isometry `Work.ORP311.lpExtendLie` of
`Submission.Work.ORP311.lp_extend_isometry`. -/
noncomputable def winIso (h : P311.TwistData N t) (n m : ℕ) :
    Rep.HSum (G := ↥N) (winDim n m) →ₗᵢ[ℂ] Rep.HSum (G := G) n := by
  classical
  exact ((hsumHilbertBasis (G := G) n).repr.symm.toLinearIsometry).comp
    ((lpExtendLie (winIdx N t n m) (winIdx_injective h n m)).comp
      ((hsumHilbertBasis (G := ↥N) (winDim n m)).repr.toLinearIsometry))

/-- The unfolded form of `winIso`: it is the composite of the two basis reindexings with the
"extend by zero along `winIdx`" isometry. -/
theorem winIso_apply (h : P311.TwistData N t) (n m : ℕ)
    (x : Rep.HSum (G := ↥N) (winDim n m)) :
    winIso h n m x = (hsumHilbertBasis (G := G) n).repr.symm
      (lpExtendLie (winIdx N t n m) (winIdx_injective h n m)
        ((hsumHilbertBasis (G := ↥N) (winDim n m)).repr x)) := rfl

/-- **The value of the window isometry on the basis vectors.** -/
theorem winIso_hinclude (h : P311.TwistData N t) (n m : ℕ) (c : Fin (winDim n m)) (k : ↥N) :
    winIso h n m (Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG k))
      = Rep.hinclude (G := G) n ((winDecode n m c).2)
          (Rep.deltaG (t ^ winExp m (winDecode n m c).1 * (k : G))) := by
  classical
  rw [winIso_apply]
  have h1 : (hsumHilbertBasis (G := ↥N) (winDim n m)).repr
      (Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG k))
      = lp.single 2 (k, c) 1 := by
    rw [← hsumHilbertBasis_apply (G := ↥N) (winDim n m) (k, c)]
    exact HilbertBasis.repr_self _ _
  rw [h1, lpExtendLie_single]
  rw [show lp.single 2 (winIdx N t n m (k, c)) (1 : ℂ)
      = (hsumHilbertBasis (G := G) n).repr (hsumHilbertBasis (G := G) n (winIdx N t n m (k, c)))
      from (HilbertBasis.repr_self _ _).symm]
  rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hsumHilbertBasis_apply]
  rfl

/-- The value of the window isometry on the `δ₁`-vectors of the `c`-th copy of `ℓ²(N)`. -/
theorem winIso_hdelta (h : P311.TwistData N t) (n m : ℕ) (c : Fin (winDim n m)) :
    winIso h n m (Rep.hdelta (G := ↥N) (winDim n m) c)
      = Rep.hinclude (G := G) n ((winDecode n m c).2)
          (Rep.deltaG (t ^ winExp m (winDecode n m c).1)) := by
  have hd : Rep.deltaG (1 : ↥N) = delta1 (↥N) := rfl
  rw [Rep.hdelta_apply, ← hd, winIso_hinclude]
  simp

/-! ### The bottom coordinates and the certificate projection -/

/-- **Conjugation by the powers of `t` preserves `N`**: `t^j x t^{-j} ∈ N` for `x ∈ N`, the
`ℤ`-indexed form of the `TwistData.conj`/`TwistData.conj_inv` fields. -/
theorem zpow_conj_mem_twist (h : P311.TwistData N t) (j : ℤ) {x : G} (hx : x ∈ N) :
    t ^ j * x * t ^ (-j) ∈ N := by
  have ht : t ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact h.conj y
    · intro hy
      have h1 := h.conj_inv (t * y * t⁻¹) hy
      simpa [mul_assoc] using h1
  have htj : t ^ j ∈ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normalizer (N : Set G)).zpow_mem ht j
  have h2 := (Subgroup.mem_normalizer_iff.mp htj x).mp hx
  rwa [← zpow_neg] at h2

/-- The bottom coset index: the index of the window with exponent `-m`. -/
def winBot (m : ℕ) : Fin (2 * m + 1) := ⟨0, by omega⟩

theorem winExp_winBot (m : ℕ) : winExp m (winBot m) = -((m : ℤ)) := by
  simp [winExp, winBot]

theorem winExp_eq_neg_iff {m : ℕ} {j : Fin (2 * m + 1)} :
    winExp m j = -((m : ℤ)) ↔ j = winBot m := by
  constructor
  · intro hj
    exact winExp_injective m (by rw [hj, winExp_winBot])
  · rintro rfl
    exact winExp_winBot m

/-- **The bottom coordinates**: the `n` coordinates of `HSum (G) (n(2m+1))` that sit in the
coset `N t^{-m}`, i.e. those `c` with `winExp m (winDecode c).1 = -m`. -/
noncomputable def botCoord (n m : ℕ) (i : Fin n) : Fin (winDim n m) :=
  (winDecode n m).symm (winBot m, i)

@[simp]
theorem winDecode_botCoord (n m : ℕ) (i : Fin n) :
    winDecode n m (botCoord n m i) = (winBot m, i) :=
  (winDecode n m).apply_symm_apply _

theorem winExp_botCoord (n m : ℕ) (i : Fin n) :
    winExp m (winDecode n m (botCoord n m i)).1 = -((m : ℤ)) := by
  rw [winDecode_botCoord, winExp_winBot]

theorem botCoord_injective (n m : ℕ) : Function.Injective (botCoord n m) := by
  intro i i' h
  have h' : (winBot m, i) = (winBot m, i') := by
    rw [← winDecode_botCoord, h, winDecode_botCoord]
  exact ((Prod.mk.injEq _ _ _ _).mp h').2

/-- The bottom coordinate of an arbitrary `c` whose exponent is `-m`. -/
theorem eq_botCoord_of_winExp {n m : ℕ} {c : Fin (winDim n m)}
    (hc : winExp m (winDecode n m c).1 = -((m : ℤ))) :
    c = botCoord n m (winDecode n m c).2 := by
  have h1 : (winDecode n m c).1 = winBot m := winExp_eq_neg_iff.mp hc
  have h2 : winDecode n m c = (winBot m, (winDecode n m c).2) := Prod.ext h1 rfl
  have h3 := winDecode_botCoord n m (winDecode n m c).2
  exact (winDecode n m).injective (by rw [h3, h2])

/-- **The certificate projection**: the orthogonal projection onto the `n` bottom coordinates
(those in the coset `N t^{-m}`). -/
noncomputable def botProj (n m : ℕ) :
    Rep.HSum (G := G) (winDim n m) →L[ℂ] Rep.HSum (G := G) (winDim n m) :=
  ∑ i : Fin n, (Rep.hinclude (G := G) (winDim n m) (botCoord n m i)).comp
    (Rep.hcoord (G := G) (winDim n m) (botCoord n m i))

/-- `botProj` kills the coordinates outside the bottom ones. -/
theorem hcoord_botProj_eq_zero (n m : ℕ) {c : Fin (winDim n m)}
    (hc : ∀ i : Fin n, c ≠ botCoord n m i) (x : Rep.HSum (G := G) (winDim n m)) :
    Rep.hcoord (G := G) (winDim n m) c (botProj (G := G) (n := n) (m := m) x) = 0 := by
  rw [botProj, sum_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ContinuousLinearMap.comp_apply, Rep.hcoord_hinclude, if_neg (hc i)]

/-- `botProj` fixes the bottom coordinates. -/
theorem hcoord_botProj_self (n m : ℕ) (i : Fin n) (x : Rep.HSum (G := G) (winDim n m)) :
    Rep.hcoord (G := G) (winDim n m) (botCoord n m i)
        (botProj (G := G) (n := n) (m := m) x)
      = Rep.hcoord (G := G) (winDim n m) (botCoord n m i) x := by
  rw [botProj, sum_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [ContinuousLinearMap.comp_apply, Rep.hcoord_hinclude, if_pos rfl]
  · intro j _ hj
    rw [ContinuousLinearMap.comp_apply, Rep.hcoord_hinclude, if_neg]
    intro hcon
    exact hj (botCoord_injective n m hcon).symm
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The certificate projection is the identity on vectors killed by it. -/
theorem botProj_eq_zero_iff (n m : ℕ) (x : Rep.HSum (G := G) (winDim n m)) :
    botProj (G := G) (n := n) (m := m) x = 0 ↔
      ∀ i : Fin n, Rep.hcoord (G := G) (winDim n m) (botCoord n m i) x = 0 := by
  constructor
  · intro h i
    rw [← hcoord_botProj_self n m i x, h, map_zero]
  · intro h
    apply Rep.hsum_ext
    intro c
    rw [map_zero]
    by_cases hc : ∃ i : Fin n, c = botCoord n m i
    · obtain ⟨i, rfl⟩ := hc
      rw [hcoord_botProj_self n m i x, h i]
    · push Not at hc
      exact hcoord_botProj_eq_zero n m hc x

/-- **The certificate.**  If the certificate projection kills a vector of the window coordinates,
then the transported vector is orthogonal to the bottom coset. -/
theorem botProj_eq_zero_of_winExp (n m : ℕ) {x : Rep.HSum (G := G) (winDim n m)}
    (hx : botProj (G := G) (n := n) (m := m) x = 0) {c : Fin (winDim n m)}
    (hc : winExp m (winDecode n m c).1 = -((m : ℤ))) :
    Rep.hcoord (G := G) (winDim n m) c x = 0 := by
  rw [eq_botCoord_of_winExp hc, ← hcoord_botProj_self n m (winDecode n m c).2 x, hx, map_zero]

/-- The certificate projection is equivariant for the right regular action. -/
theorem botProj_equivariant (n m : ℕ) :
    Rep.Equivariant (G := G) (botProj (G := G) (n := n) (m := m)) := by
  intro g
  apply ContinuousLinearMap.ext
  intro x
  apply Rep.hsum_ext
  intro c
  by_cases hc : ∃ i : Fin n, c = botCoord n m i
  · obtain ⟨i, rfl⟩ := hc
    have h1 : Rep.hcoord (G := G) (winDim n m) (botCoord n m i)
        (botProj (G := G) (n := n) (m := m) (Rep.diagOp (G := G) (winDim n m) g x))
        = Rep.rightRegOp g (Rep.hcoord (G := G) (winDim n m) (botCoord n m i) x) := by
      rw [hcoord_botProj_self n m i (Rep.diagOp (G := G) (winDim n m) g x)]
      exact Rep.hcoord_diagOp_apply (G := G) (winDim n m) g (botCoord n m i) x
    have h2 : Rep.hcoord (G := G) (winDim n m) (botCoord n m i)
        (Rep.diagOp (G := G) (winDim n m) g (botProj (G := G) (n := n) (m := m) x))
        = Rep.rightRegOp g (Rep.hcoord (G := G) (winDim n m) (botCoord n m i) x) := by
      rw [Rep.hcoord_diagOp_apply, hcoord_botProj_self n m i x]
    rw [ContinuousLinearMap.comp_apply]
    exact h1.trans h2.symm
  · push Not at hc
    have h2 : Rep.hcoord (G := G) (winDim n m) c
        (Rep.diagOp (G := G) (winDim n m) g (botProj (G := G) (n := n) (m := m) x)) = 0 := by
      rw [Rep.hcoord_diagOp_apply, hcoord_botProj_eq_zero n m hc, map_zero]
    rw [ContinuousLinearMap.comp_apply]
    exact (hcoord_botProj_eq_zero n m hc (Rep.diagOp (G := G) (winDim n m) g x)).trans h2.symm

/-- The `δ_c`-vector of a non-bottom coordinate is orthogonal to the range of the certificate
projection. -/
theorem inner_botProj_hdelta_eq_zero (n m : ℕ) {c : Fin (winDim n m)}
    (hc : ∀ i : Fin n, c ≠ botCoord n m i) (z : Rep.HSum (G := G) (winDim n m)) :
    inner ℂ (botProj (G := G) (n := n) (m := m) z) (Rep.hdelta (G := G) (winDim n m) c) = 0 := by
  rw [botProj, sum_apply, sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ContinuousLinearMap.comp_apply, inner_hinclude, Rep.hcoord_hdelta,
    if_neg (fun h => hc i h.symm)]
  simp

/-! ### The window sits in the range of the window isometry -/

/-- The range of the window isometry is closed: it is the image of the complete space
`HSum (G := ↥N) (winDim n m)` under an isometry, hence closed in the complete space
`HSum (G := G) n`. -/
private theorem winIso_range_isClosed {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G}
    (h : P311.TwistData N t) (n m : ℕ) :
    IsClosed ((LinearMap.range (winIso h n m).toLinearMap : Submodule ℂ (Rep.HSum (G := G) n)) :
      Set (Rep.HSum (G := G) n)) := by
  rw [LinearMap.coe_range]
  exact (LinearIsometry.isometry (winIso h n m)).antilipschitz.isClosed_range
    (Isometry.uniformContinuous (LinearIsometry.isometry (winIso h n m)))

/-- **Every window vector is in the range of the window isometry.**  Each generator
`e_i ⊗ δ_g` with `g = n' t^j ∈ window N t m` (`|j| ≤ m`) is the image of the basis vector
`e_c ⊗ δ_k` of the `c`-th copy of `ℓ²(N)`, where `c` is the coordinate with exponent `j` and
second index `i`, and `k = t^{-j} n' t^j ∈ N` (by `zpow_conj_mem_twist`).  Since the range is closed,
the whole closed span `ell2Sub n (window N t m)` is contained in it. -/
private theorem window_le_range_winIso {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G}
    (h : P311.TwistData N t) (n m : ℕ) :
    ell2Sub (G := G) n (window N t m) ≤ LinearMap.range (winIso h n m).toLinearMap := by
  classical
  refine Submodule.topologicalClosure_minimal (Submodule.span ℂ _) ?_
    (winIso_range_isClosed h n m)
  rw [Submodule.span_le]
  rintro w ⟨g, hg, i, rfl⟩
  obtain ⟨n', j, hj1, hj2, hg⟩ := hg
  have hj0 : 0 ≤ j + (m : ℤ) := by omega
  set jj : Fin (2 * m + 1) := ⟨(j + (m : ℤ)).toNat, by omega⟩
  have hjj : winExp m jj = j := by
    simp only [winExp, jj]
    rw [Int.toNat_of_nonneg hj0]
    ring
  let k : ↥N := ⟨t ^ (-j) * (n' : G) * t ^ j, by
    simpa using zpow_conj_mem_twist h (-j) n'.2⟩
  refine ⟨Rep.hinclude (G := ↥N) (winDim n m) ((winDecode n m).symm (jj, i))
    (Rep.deltaG k), ?_⟩
  change winIso h n m (Rep.hinclude (G := ↥N) (winDim n m) ((winDecode n m).symm (jj, i))
    (Rep.deltaG k)) = _
  rw [winIso_hinclude]
  simp only [Equiv.apply_symm_apply]
  rw [hjj]
  have hkg : t ^ j * (k : G) = g := by
    rw [hg]
    have h1 : t ^ j * (k : G) = (t ^ j * t ^ (-j)) * ((n' : G) * t ^ j) := by
      simp only [k]
      noncomm_ring
    rw [h1, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  rw [hkg]

/-! ### The pieces of the Følner transport, kept private

The four lemmas below (`diagOp_comp_winIso`, `hdim_comap_winIso`,
`winIso_mem_orthogonal_coset_bot` and the reindexing `sum_sWin_eq_sum_fin`) are also available
as public lemmas in the sibling modules `Submission.Work.ORP311.diagOp_comp_winIso`,
`Submission.Work.ORP311.hdim_comap_winIso` and
`Submission.Work.ORP311.winIso_mem_orthogonal_coset_bot`.  Those modules import this one (they
need the definitions `winIso`, `winDim`, `winExp`, …), so this module cannot import them back;
their statements are reproduced here, privately, so that the main theorem below is
self-contained. -/

private theorem diagOp_comp_winIso {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n m : ℕ) (k : ↥N) (x : Work.ORVonNeumann.Rep.HSum (G := ↥N) (Work.ORP311.winDim n m)) : Work.ORP311.winIso h n m (Work.ORVonNeumann.Rep.diagOp (G := ↥N) (Work.ORP311.winDim n m) k x) = Work.ORVonNeumann.Rep.diagOp (G := G) n (k : G) (Work.ORP311.winIso h n m x) := by
  classical
  -- The basis vectors `e_c ⊗ δ_g` span a dense subspace of `HSum (G := ↥N) (winDim n m)`.
  have hDense : Dense (Submodule.span ℂ
      (Set.range (hsumHilbertBasis (G := ↥N) (winDim n m))) :
      Set (Rep.HSum (G := ↥N) (winDim n m))) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact HilbertBasis.dense_span _
  have hbasis : ∀ (g : ↥N) (c : Fin (winDim n m)),
      hsumHilbertBasis (G := ↥N) (winDim n m) (g, c)
        = Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG g) := by
    intro g c
    simpa using hsumHilbertBasis_apply (G := ↥N) (winDim n m) (g, c)
  have hfg : (winIso h n m).toContinuousLinearMap.comp (Rep.diagOp (G := ↥N) (winDim n m) k)
      = (Rep.diagOp (G := G) n (k : G)).comp (winIso h n m).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on hDense
    rintro y ⟨p, rfl⟩
    obtain ⟨g, c⟩ := p
    rw [hbasis g c]
    simp only [ContinuousLinearMap.comp_apply]
    change (winIso h n m)
        (Rep.diagOp (G := ↥N) (winDim n m) k
          (Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG g)))
      = Rep.diagOp (G := G) n (k : G)
          (winIso h n m (Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG g)))
    -- The two actions on the basis vector `e_c ⊗ δ_g`.
    have h1 : Rep.diagOp (G := ↥N) (winDim n m) k
        (Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG g))
        = Rep.hinclude (G := ↥N) (winDim n m) c (Rep.deltaG (g * k⁻¹)) := by
      have hh := congrArg
        (fun f : Work.ORVonNeumann.l2 ↥N →L[ℂ] Rep.HSum (G := ↥N) (winDim n m) =>
          f (Rep.deltaG g))
        (Rep.diagOp_hinclude (G := ↥N) (winDim n m) k c)
      simpa only [ContinuousLinearMap.comp_apply, Rep.rightRegOp_deltaG] using hh
    have h2 : Rep.diagOp (G := G) n (k : G)
        (Rep.hinclude (G := G) n (winDecode n m c).2
          (Rep.deltaG (t ^ winExp m (winDecode n m c).1 * (g : G))))
        = Rep.hinclude (G := G) n (winDecode n m c).2
            (Rep.deltaG ((t ^ winExp m (winDecode n m c).1 * (g : G)) * (k : G)⁻¹)) := by
      have hh := congrArg
        (fun f : Work.ORVonNeumann.l2 G →L[ℂ] Rep.HSum (G := G) n =>
          f (Rep.deltaG (t ^ winExp m (winDecode n m c).1 * (g : G))))
        (Rep.diagOp_hinclude (G := G) n (k : G) (winDecode n m c).2)
      simpa only [ContinuousLinearMap.comp_apply, Rep.rightRegOp_deltaG] using hh
    have harg : t ^ winExp m (winDecode n m c).1 * ((g * k⁻¹ : ↥N) : G)
        = (t ^ winExp m (winDecode n m c).1 * (g : G)) * (k : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rw [h1, winIso_hinclude h n m c (g * k⁻¹), winIso_hinclude h n m c g, h2, harg]
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    using DFunLike.congr_fun hfg x

private theorem sum_sWin_eq_sum_fin {G : Type*} [Group G] {N : Subgroup G} {t : G}
    (h : Work.ORP311.P311.TwistData N t) (m : ℕ) (f : G → ℝ) :
    ∑ g ∈ Work.ORP311.P311.sWin t m, f g
      = ∑ j : Fin (2 * m + 1), f (t ^ Work.ORP311.winExp m j) := by
  classical
  rw [Work.ORP311.P311.sWin, Finset.sum_image (injOn_zpow_Icc h m)]
  symm
  refine Finset.sum_bij (fun j (_ : j ∈ Finset.univ) => Work.ORP311.winExp m j) (fun j _ => ?_)
    (fun a _ b _ hab => ?_) (fun b hb => ?_) (fun a _ => ?_)
  · exact Finset.mem_Icc.mpr (Work.ORP311.winExp_mem m j)
  · exact Work.ORP311.winExp_injective m hab
  · obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
    refine ⟨⟨(b + m).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [Int.toNat_lt (by omega)]; omega
    · simp only [Work.ORP311.winExp]; rw [Int.toNat_of_nonneg (by omega)]; ring
  · rfl

private theorem hdim_comap_winIso {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n m : ℕ) (V : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [V.HasOrthogonalProjection] [(V.comap (Work.ORP311.winIso h n m).toLinearMap).HasOrthogonalProjection] (hV : V ≤ LinearMap.range (Work.ORP311.winIso h n m).toLinearMap) : Work.ORVonNeumann.Rep.hdim (G := ↥N) (V.comap (Work.ORP311.winIso h n m).toLinearMap) = Work.ORP311.tDim (G := G) n (Work.ORP311.P311.sWin t m) V := by
  classical
  -- The left-hand side is the sum of the squared norms of the projections of the `δ`-vectors of
  -- the `n(2m+1)` coordinates; the window isometry sends the `c`-th coordinate of `ℓ²(N)` onto
  -- the `δ`-vector at `t^{j(c)}` in the `i(c)`-th coordinate of `ℓ²(G)`, and projecting before or
  -- after the isometry gives the same norms.
  have hL : ∑ c : Fin (winDim n m),
        ‖(V.comap (winIso h n m).toLinearMap).starProjection (Rep.hdelta (G := ↥N) (winDim n m) c)‖ ^ 2
      = ∑ j : Fin (2 * m + 1), ∑ i : Fin n,
        ‖V.starProjection (Rep.hinclude (G := G) n i (Rep.deltaG (t ^ winExp m j)))‖ ^ 2 := by
    have hcong : ∀ c : Fin (winDim n m),
        ‖(V.comap (winIso h n m).toLinearMap).starProjection (Rep.hdelta (G := ↥N) (winDim n m) c)‖ ^ 2
        = ‖V.starProjection (Rep.hinclude (G := G) n (winDecode n m c).2
            (Rep.deltaG (t ^ winExp m (winDecode n m c).1)))‖ ^ 2 := by
      intro c
      have h1 : (winIso h n m) ((V.comap (winIso h n m).toLinearMap).starProjection
            (Rep.hdelta (G := ↥N) (winDim n m) c))
          = V.starProjection ((winIso h n m) (Rep.hdelta (G := ↥N) (winDim n m) c)) :=
        starProjection_comap_isometry (winIso h n m) V hV (Rep.hdelta (G := ↥N) (winDim n m) c)
      have h2 : ‖(V.comap (winIso h n m).toLinearMap).starProjection (Rep.hdelta (G := ↥N) (winDim n m) c)‖
          = ‖V.starProjection ((winIso h n m) (Rep.hdelta (G := ↥N) (winDim n m) c))‖ := by
        rw [← h1, (winIso h n m).norm_map]
      rw [h2, winIso_hdelta]
    have hre : ∑ c : Fin (winDim n m),
        ‖V.starProjection (Rep.hinclude (G := G) n (winDecode n m c).2
          (Rep.deltaG (t ^ winExp m (winDecode n m c).1)))‖ ^ 2
      = ∑ j : Fin (2 * m + 1), ∑ i : Fin n,
        ‖V.starProjection (Rep.hinclude (G := G) n i (Rep.deltaG (t ^ winExp m j)))‖ ^ 2 := by
      let F : Fin (2 * m + 1) × Fin n → ℝ :=
        fun p => ‖V.starProjection (Rep.hinclude (G := G) n p.2 (Rep.deltaG (t ^ winExp m p.1)))‖ ^ 2
      calc ∑ c : Fin (winDim n m),
            ‖V.starProjection (Rep.hinclude (G := G) n (winDecode n m c).2
              (Rep.deltaG (t ^ winExp m (winDecode n m c).1)))‖ ^ 2
          = ∑ c : Fin (winDim n m), F (winDecode n m c) := rfl
        _ = ∑ p : Fin (2 * m + 1) × Fin n, F p := Equiv.sum_comp (winDecode n m) F
        _ = ∑ j : Fin (2 * m + 1), ∑ i : Fin n, F (j, i) := Fintype.sum_prod_type F
        _ = ∑ j : Fin (2 * m + 1), ∑ i : Fin n,
              ‖V.starProjection (Rep.hinclude (G := G) n i (Rep.deltaG (t ^ winExp m j)))‖ ^ 2 := rfl
    exact (Finset.sum_congr rfl (fun c _ => hcong c)).trans hre
  -- The right-hand side is the same double sum, evaluated on the transversal `sWin t m`.
  have hR : ∑ g ∈ P311.sWin t m, ∑ i : Fin n,
        ‖V.starProjection (Rep.hinclude (G := G) n i (Rep.deltaG g))‖ ^ 2
      = ∑ j : Fin (2 * m + 1), ∑ i : Fin n,
        ‖V.starProjection (Rep.hinclude (G := G) n i (Rep.deltaG (t ^ winExp m j)))‖ ^ 2 :=
    sum_sWin_eq_sum_fin h m (fun g => ∑ i : Fin n,
      ‖V.starProjection (Rep.hinclude (G := G) n i (Rep.deltaG g))‖ ^ 2)
  rw [Rep.hdim_apply, tDim_apply]
  exact hL.trans hR.symm

private theorem exists_zpow_mul_of_mem_coset {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G}
    (h : P311.TwistData N t) (m : ℕ) {g : G}
    (hg : g ∈ coset N t (-((m : ℤ)))) :
    ∃ k : ↥N, g = t ^ (-((m : ℤ))) * (k : G) := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨⟨t ^ ((m : ℤ)) * (n : G) * t ^ (-((m : ℤ))),
    zpow_conj_mem_twist h (m : ℤ) n.2⟩, ?_⟩
  rw [hn]
  have h1 : t ^ (-((m : ℤ))) * t ^ ((m : ℤ)) = 1 := by
    rw [← zpow_add, neg_add_cancel, zpow_zero]
  calc (n : G) * t ^ (-((m : ℤ)))
      = (t ^ (-((m : ℤ))) * t ^ ((m : ℤ))) * ((n : G) * t ^ (-((m : ℤ)))) := by
        rw [h1, one_mul]
    _ = t ^ (-((m : ℤ))) * (t ^ ((m : ℤ)) * (n : G) * t ^ (-((m : ℤ)))) := by
        simp only [mul_assoc]

private theorem winIso_hinclude_bot {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G}
    (h : P311.TwistData N t) (n m : ℕ) (i : Fin n) (k : ↥N) :
    winIso h n m (Rep.hinclude (G := ↥N) (winDim n m) (botCoord n m i) (Rep.deltaG k))
      = Rep.hinclude (G := G) n i (Rep.deltaG (t ^ (-((m : ℤ))) * (k : G))) := by
  rw [winIso_hinclude]
  simp [winDecode_botCoord, winExp_winBot]

private theorem winIso_mem_orthogonal_coset_bot {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n m : ℕ) {x : Work.ORVonNeumann.Rep.HSum (G := ↥N) (Work.ORP311.winDim n m)} (hx : ∀ c : Fin (Work.ORP311.winDim n m), Work.ORP311.winExp m (Work.ORP311.winDecode n m c).1 = -((m : ℤ)) → Work.ORVonNeumann.Rep.hcoord (G := ↥N) (Work.ORP311.winDim n m) c x = 0) : Work.ORP311.winIso h n m x ∈ (Work.ORP311.ell2Sub (G := G) n (Work.ORP311.coset N t (-((m : ℤ)))))ᗮ := by
  -- `(ell2Sub n Z)ᗮ = ell2Sub n Zᶜ`, so it suffices to test against the basis vectors `δ_g`,
  -- `g ∈ Z`, which is what `mem_ell2Sub_iff` provides.
  have hZc : ell2Sub (G := G) n (coset N t (-((m : ℤ))))ᶜ
      = (ell2Sub (G := G) n (coset N t (-((m : ℤ)))))ᗮ := by
    rw [ell2Sub_orthogonal n (coset N t (-((m : ℤ))))ᶜ, compl_compl]
  rw [← hZc, mem_ell2Sub_iff]
  intro g hg i
  -- `g` lies in the bottom coset, so `g = t^{-m} k` for some `k ∈ N`.
  have hgZ : g ∈ coset N t (-((m : ℤ))) := by simpa using hg
  obtain ⟨k, hk⟩ := exists_zpow_mul_of_mem_coset h m hgZ
  -- swap the pairing and pass to the spanning vector `hinclude i (δ_g)`
  rw [inner_eq_zero_comm, ← inner_hinclude]
  -- that vector is `winIso` of the `i`-th bottom coordinate applied to `δ_k`
  rw [hk, ← winIso_hinclude_bot h n m i k, LinearIsometry.inner_map_map, inner_hinclude,
    hx (botCoord n m i) (winExp_botCoord n m i), inner_zero_right]

/-! ### The window dimension bound -/

/-- The comap of a closed subspace under the window isometry is again closed: `winIso` is a
continuous linear map and its domain is complete. -/
theorem comap_winIso_hasOrthogonalProjection (h : P311.TwistData N t) (n m : ℕ)
    (V : Submodule ℂ (Rep.HSum (G := G) n)) [V.HasOrthogonalProjection] :
    (V.comap (winIso h n m).toLinearMap).HasOrthogonalProjection := by
  have hVclosed : IsClosed (V : Set (Rep.HSum (G := G) n)) := by
    have h1 : (V : Set (Rep.HSum (G := G) n))
        = {x : Rep.HSum (G := G) n | (1 - V.starProjection : _ →L[ℂ] _) x = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, sub_apply, one_apply_eq_self, sub_eq_zero]
      constructor
      · intro hx; exact (Submodule.starProjection_eq_self_iff.mpr hx).symm
      · intro hx; exact Submodule.starProjection_eq_self_iff.mp hx.symm
    rw [h1]
    exact ContinuousLinearMap.isClosed_ker _
  have h2 : IsClosed ((V.comap (winIso h n m).toLinearMap :
      Submodule ℂ (Rep.HSum (G := ↥N) (winDim n m))) :
      Set (Rep.HSum (G := ↥N) (winDim n m))) := by
    rw [Submodule.comap_coe]
    exact hVclosed.preimage (winIso h n m).continuous
  haveI : CompleteSpace ↥(V.comap (winIso h n m).toLinearMap) := h2.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

theorem tDim_le_of_bottom_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n m : ℕ) (V : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [V.HasOrthogonalProjection] (hVsub : V ≤ Work.ORP311.ell2Sub (G := G) n (Work.ORP311.window N t m)) (hVinv : ∀ k : G, k ∈ N → ∀ x ∈ V, Work.ORVonNeumann.Rep.diagOp (G := G) n k x ∈ V) (hinj : ∀ x ∈ V, Work.ORP311.P311.blk n N t (-(m:ℤ)) x = 0 → x = 0) : Work.ORP311.tDim (G := G) n (Work.ORP311.P311.sWin t m) V ≤ (n : ℝ) := by
  classical
  -- The window is contained in the range of the window isometry.
  have hrange := window_le_range_winIso h n m
  have hVrange : V ≤ LinearMap.range (winIso h n m).toLinearMap := fun x hx => hrange (hVsub hx)
  haveI : (V.comap (winIso h n m).toLinearMap).HasOrthogonalProjection :=
    comap_winIso_hasOrthogonalProjection h n m V
  set V' := V.comap (winIso h n m).toLinearMap with hV'def
  set S : Finset (Fin (winDim n m)) := Finset.univ.image (botCoord n m) with hSdef
  -- * `V'` is invariant under the right `N`-action.
  have hV'inv : ∀ k : ↥N, ∀ x ∈ V', Rep.diagOp (G := ↥N) (winDim n m) k x ∈ V' := by
    intro k x hx
    have hx' : winIso h n m x ∈ V := by
      rw [hV'def, Submodule.mem_comap] at hx
      exact hx
    rw [hV'def, Submodule.mem_comap]
    show winIso h n m (Rep.diagOp (G := ↥N) (winDim n m) k x) ∈ V
    rw [diagOp_comp_winIso h n m k x]
    exact hVinv (k : G) k.2 _ hx'
  -- * The bottom-coordinate projection detects `0` on `V'`, by the injectivity of `blk (-m)`.
  have hcert : ∀ x ∈ V', botProj (G := ↥N) (n := n) (m := m) x = 0 → x = 0 := by
    intro x hx h0
    have hxcoord : ∀ c : Fin (winDim n m), winExp m (winDecode n m c).1 = -((m : ℤ)) →
        Rep.hcoord (G := ↥N) (winDim n m) c x = 0 :=
      fun c hc => botProj_eq_zero_of_winExp n m h0 hc
    have horth : winIso h n m x ∈ (ell2Sub (G := G) n (coset N t (-((m : ℤ)))))ᗮ :=
      winIso_mem_orthogonal_coset_bot h n m hxcoord
    have hblk : P311.blk n N t (-(m : ℤ)) (winIso h n m x) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr horth
    have hxV : winIso h n m x ∈ V := by
      rw [hV'def, Submodule.mem_comap] at hx
      exact hx
    exact (winIso h n m).injective (by rw [hinj _ hxV hblk, map_zero])
  -- * The dimension-theoretic injectivity bound.
  have hboteq : Rep.Equivariant (G := ↥N) (botProj (G := ↥N) (n := n) (m := m)) :=
    botProj_equivariant (G := ↥N) n m
  have hdim_le := hdim_le_hdim_range_of_injective (G := ↥N)
    (botProj (G := ↥N) (n := n) (m := m)) hboteq V' hV'inv hcert
  -- * The range of the certificate lives in the `n` bottom coordinates.
  have hle : Rep.hdim (G := ↥N)
      (((botProj (G := ↥N) (n := n) (m := m)).comp V'.starProjection).range.topologicalClosure)
      ≤ (S.card : ℝ) := by
    refine hdim_le_card_of_orthogonal_delta (G := ↥N)
      (((botProj (G := ↥N) (n := n) (m := m)).comp V'.starProjection).range.topologicalClosure)
      S ?_
    intro c hc
    have hc' : ∀ i : Fin n, c ≠ botCoord n m i := by
      intro i hci
      exact hc (by rw [hSdef]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hci.symm⟩)
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    change inner ℂ (Rep.hdelta (G := ↥N) (winDim n m) c)
      ((botProj (G := ↥N) (n := n) (m := m)) (V'.starProjection x)) = 0
    rw [inner_eq_zero_comm]
    exact inner_botProj_hdelta_eq_zero n m hc' (V'.starProjection x)
  have hcard : S.card = n := by
    rw [hSdef, Finset.card_image_of_injOn (f := botCoord n m) (s := Finset.univ)
      (fun i _ j _ hij => botCoord_injective n m hij), Finset.card_univ, Fintype.card_fin]
  have hcardR : (S.card : ℝ) = (n : ℝ) := by rw [hcard]
  -- * The transported dimension is the transversal dimension.
  have hmain : Rep.hdim (G := ↥N) V' = tDim (G := G) n (P311.sWin t m) V :=
    hdim_comap_winIso h n m V hVrange
  linarith [hdim_le, hle, hcardR, hmain]

end Work.ORP311
