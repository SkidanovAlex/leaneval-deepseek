import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.coordP_level_eq
import Submission.Work.Pert.pert2v2.Rlow_phi_translate

/-!
# `Work.Pert.pert2v2.orbit_mem` — the third conjunct of `PertData.orbit`, via the gate level

## The problem

`PertData.orbit`'s conclusion carries the extra clause

  `∀ i < n, f^[i] (φ w) ∈ Df`

(the formalisation records that the `n` iterates of `f` applied to `φ w` are honest values of the
perturbation, not junk of the total function `f`).  Neither `w ∈ Dφ` nor `w' ∈ Dφ` gives it
directly: `GoodP`/`mIdxP` control the orbit of the *seed* below the level of the point, i.e. the
**past** of `φ w`, whereas the clause is about its **future**.

## The mechanism (this file)

Let `Q` be the gate on which `Φ` is a Fatou coordinate of the lift `F`, `τ` the chart with
`τ ∘ F = f ∘ τ` on `Q`, and suppose the coordinate `φ = coordP f Df τ Φ Q` is used.  The single
structural fact that closes the gap is

  **`τ '' Q ⊆ Df`**  (`hτDf`),

which the assembly has (`tauC '' Qm Ξ' α ⊆ ball 0 rr ⊆ L ⊆ Df`).  Then:

* the *walk* `F^j u ∈ Q` (`j ≤ k`) gives `f^j (τ u) = τ (F^j u) ∈ Df` — the low part of the orbit
  is covered **for free**, because the `τ`-images of the whole gate sit inside `Df`;
* the *upper* part is covered by the orbit condition of the minimal level of `w'`
  (`GoodP`), transported along the `F`-orbit that relates the gate point `u` of `w'` at the level
  `N` to the minimal-level gate point `ς_min` of `w'` (`hOrb`).

The two intervals of indices tile `{0, …, N-1}` in both cases of the level comparison, so no
hypothesis is left over.

Concretely `orbit_mem_of_level` proves:

  `Φ u = w' - N`, `u ∈ Q`, `GoodP f Df τ Φ Q w'`  ⟹  `∀ i < N, f^[i] (τ u) ∈ Df`.

## Consequence for `orbit`

`orbit_one_of_level` assembles the `m = 1` instance of the contract's `orbit` at a low piece whose
level presentation is `R w + m = Φ u` with `τ u = f^[m] (φ w)` (the crux's `τ ζ_w = f^[m] (φ w)`,
`u = Tt α ζ_w`): with `N := n - m ≥ 0` one gets `φ w' = f^[n] (φ w)` from `coordP_level_eq`, and the
membership clause from `orbit_mem_of_level` above together with the crux's `LowClause`
(`∀ j ≤ m, f^[j] (φ w) ∈ Df`) — the two pieces of the index range `{0, …, n-1}` being
`{0, …, m}` (crux) and `{m, …, n-1}` (`f^{i-m} (τ u)`).
-/

namespace Work.Pert.pert2v2

open Work.Pert Complex Set

noncomputable section

/-- **Orbit membership across a gate level.**  If `u` is the gate point of `w'` at the level `N`
(`Φ u = w' - N`) and `w'` is an admissible point of the coordinate (`GoodP`), then the whole orbit
of `τ u` up to time `N` stays in `Df`.

The two inputs beyond the level structure are `τ '' Q ⊆ Df` (the walk part) and the orbit condition
of the minimal level of `w'` (the far part). -/
theorem orbit_mem_of_level {f F τ Φ : ℂ → ℂ} {Df Q : Set ℂ} {u w' : ℂ} {N : ℕ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hτDf : ∀ z ∈ Q, τ z ∈ Df)
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hu : u ∈ Q) (hN : Φ u = w' - (N : ℂ))
    (hw' : Work.Pert.GoodP f Df τ Φ Q w') :
    ∀ i : ℕ, i < N → f^[i] (τ u) ∈ Df := by
  classical
  -- injectivity of `Φ` on the gate, from the orbit rule at `k = 0`
  have hinjQ : Set.InjOn Φ Q := fun z hz z' hz' hzz' => by
    have h := (hOrb z hz z' hz' 0 (by rw [hzz']; simp)).2
    simpa using h
  -- the minimal level of `w'` and its gate point
  obtain ⟨himg, horbmin⟩ := Work.Pert.mIdxP_spec hw'
  obtain ⟨ς, hςQ, hςΦ⟩ := himg
  have hseed : Work.Pert.seedP τ Φ Q (w' - ((Work.Pert.mIdxP f Df τ Φ Q w' : ℕ) : ℂ)) = τ ς :=
    Work.Pert.seedP_eq_of_mem' hinjQ ⟨ς, hςQ, hςΦ⟩ hςQ hςΦ
  have horb : ∀ j : ℕ, j < Work.Pert.mIdxP f Df τ Φ Q w' → f^[j] (τ ς) ∈ Df := by
    intro j hj
    have h := horbmin j hj
    rwa [hseed] at h
  by_cases hle : Work.Pert.mIdxP f Df τ Φ Q w' ≤ N
  · -- ## the level `N` is above the minimal level: walk `u` up to `ς`
    have hcast : ((N - Work.Pert.mIdxP f Df τ Φ Q w' : ℕ) : ℂ)
        = (N : ℂ) - ((Work.Pert.mIdxP f Df τ Φ Q w' : ℕ) : ℂ) := by
      rw [Nat.cast_sub hle]
    have hEq : Φ ς = Φ u + ((N - Work.Pert.mIdxP f Df τ Φ Q w' : ℕ) : ℂ) := by
      rw [hςΦ, hN, hcast]
      ring
    obtain ⟨hwalk, hfin⟩ :=
      hOrb u hu ς hςQ (N - Work.Pert.mIdxP f Df τ Φ Q w') hEq
    -- `τ u` is the `K`-th backward iterate of `τ ς`
    have hτwalk : τ (F^[N - Work.Pert.mIdxP f Df τ Φ Q w'] u)
        = f^[N - Work.Pert.mIdxP f Df τ Φ Q w'] (τ u) :=
      Work.Pert.tau_walk_iterate hwalk hτF
    have hτς : f^[N - Work.Pert.mIdxP f Df τ Φ Q w'] (τ u) = τ ς := by
      rw [← hτwalk, hfin]
    intro i hi
    rcases le_or_gt i (N - Work.Pert.mIdxP f Df τ Φ Q w') with hicase | hicase
    · -- the walk part
      have hmem : F^[i] u ∈ Q := hwalk i hicase
      have : f^[i] (τ u) = τ (F^[i] u) := (Work.Pert.tau_walk_iterate
        (fun j hj => hwalk j (le_trans hj hicase)) hτF).symm
      rw [this]
      exact hτDf _ hmem
    · -- the far part, transported along the orbit
      have hsub : N - Work.Pert.mIdxP f Df τ Φ Q w' < i := hicase
      have hlt : i - (N - Work.Pert.mIdxP f Df τ Φ Q w')
          < Work.Pert.mIdxP f Df τ Φ Q w' := by omega
      have hsplit : f^[i] (τ u) = f^[i - (N - Work.Pert.mIdxP f Df τ Φ Q w')]
          (f^[N - Work.Pert.mIdxP f Df τ Φ Q w'] (τ u)) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hsub.le]
      rw [hsplit, hτς]
      exact horb _ hlt
  · -- ## the level `N` is below the minimal level: `u` is a forward iterate of `ς`
    have hlt : N < Work.Pert.mIdxP f Df τ Φ Q w' := not_le.mp hle
    have hcast : ((Work.Pert.mIdxP f Df τ Φ Q w' - N : ℕ) : ℂ)
        = ((Work.Pert.mIdxP f Df τ Φ Q w' : ℕ) : ℂ) - (N : ℂ) := by
      rw [Nat.cast_sub hlt.le]
    have hEq : Φ u = Φ ς + ((Work.Pert.mIdxP f Df τ Φ Q w' - N : ℕ) : ℂ) := by
      rw [hN, hςΦ, hcast]
      ring
    obtain ⟨hwalk, hfin⟩ :=
      hOrb ς hςQ u hu (Work.Pert.mIdxP f Df τ Φ Q w' - N) hEq
    have hτu : τ u = f^[Work.Pert.mIdxP f Df τ Φ Q w' - N] (τ ς) := by
      have h := Work.Pert.tau_walk_iterate hwalk hτF
      rw [← h, hfin]
    intro i hi
    have hidx : i + (Work.Pert.mIdxP f Df τ Φ Q w' - N) < Work.Pert.mIdxP f Df τ Φ Q w' := by
      omega
    have hsplit : f^[i] (τ u)
        = f^[i + (Work.Pert.mIdxP f Df τ Φ Q w' - N)] (τ ς) := by
      rw [hτu, Function.iterate_add_apply]
    rw [hsplit]
    exact horb _ hidx

/-- **The membership clause of `orbit` for a short shift.**  When the shift `n` is at most the
level `m` of the low piece, the crux's `LowClause` (`∀ j ≤ m, f^[j] (φ w) ∈ Df`) already covers the
whole range `i < n`. -/
theorem orbit_mem_le {f φ : ℂ → ℂ} {Df : Set ℂ} {w : ℂ} {m n : ℕ}
    (hlow : ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) (hn : n ≤ m) :
    ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df :=
  fun i hi => hlow i (le_trans hi.le hn)

/-- **The membership clause of `orbit` for a long shift.**  For `m ≤ n` the range `i ≤ m` comes
from the crux's `LowClause` and the range `m ≤ i < n` is the orbit of the gate value `τ u`
(`τ u = f^[m] (φ w)`), covered by `orbit_mem_of_level` as soon as `Φ u` is the level-`(n-m)` gate
value of `w'`. -/
theorem orbit_mem_low {f F τ Φ : ℂ → ℂ} {Df Q : Set ℂ} {u w w' : ℂ} {m n : ℕ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hτDf : ∀ z ∈ Q, τ z ∈ Df)
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hu : u ∈ Q) (hΦu : Φ u = w' - ((n - m : ℕ) : ℂ)) (hgoodw' : Work.Pert.GoodP f Df τ Φ Q w')
    (hτu : τ u = f^[m] (Work.Pert.coordP f Df τ Φ Q w)) (hmn : m ≤ n)
    (hlow : ∀ j : ℕ, j ≤ m → f^[j] (Work.Pert.coordP f Df τ Φ Q w) ∈ Df) :
    ∀ i : ℕ, i < n → f^[i] (Work.Pert.coordP f Df τ Φ Q w) ∈ Df := by
  intro i hi
  rcases le_or_gt i m with him | him
  · exact hlow i him
  · have hlt : i - m < n - m := by omega
    have hmem := orbit_mem_of_level hτF hτDf hOrb hu hΦu hgoodw' (i - m) hlt
    have hsplit : f^[i] (Work.Pert.coordP f Df τ Φ Q w)
        = f^[i - m] (f^[m] (Work.Pert.coordP f Df τ Φ Q w)) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel him.le]
    rw [hsplit, ← hτu]
    exact hmem

/-- **The `m = 1` instance of `PertData.orbit` for a piece with a gate level presentation.**
Suppose the piece `R` satisfies the low-piece presentation

* `R w + m = Φ u` with `u ∈ Q` and `τ u = f^[m] (φ w)`

(the crux's `u = Tt α ζ_w`, `τ ζ_w = f^[m] (φ w)`), and the shift `w' = R w + n` is at least `m`.
Then the contract's conclusion holds: `f^[n] (φ w) = φ w'` and the whole orbit of `φ w` up to `n`
stays in `Df`.

The value is `coordP_level_eq` at the level `n - m` of `w'` with gate point `u`; the memberships are
`orbit_mem_low`.  The shift `n < m` is `Work.Pert.pert2v2.Rlow_phi_translate_lt` (value) and
`orbit_mem_le` (memberships). -/
theorem orbit_one_of_level {f F τ Φ R : ℂ → ℂ} {Df Q : Set ℂ} {w w' u : ℂ} {m n : ℕ}
    (hAb : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hτDf : ∀ z ∈ Q, τ z ∈ Df)
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hu : u ∈ Q)
    (hgoodw' : Work.Pert.GoodP f Df τ Φ Q w')
    (hm : 1 ≤ m) (hmn : m ≤ n)
    (huR : R w + (m : ℂ) = Φ u)
    (hτu : τ u = f^[m] (Work.Pert.coordP f Df τ Φ Q w))
    (hnR : w' = R w + (n : ℂ))
    (hlow : ∀ j : ℕ, j ≤ m → f^[j] (Work.Pert.coordP f Df τ Φ Q w) ∈ Df) :
    f^[n] (Work.Pert.coordP f Df τ Φ Q w) = Work.Pert.coordP f Df τ Φ Q w' ∧
      ∀ i : ℕ, i < n → f^[i] (Work.Pert.coordP f Df τ Φ Q w) ∈ Df := by
  have hinjQ : Set.InjOn Φ Q := fun z hz z' hz' hzz' => by
    have h := (hOrb z hz z' hz' 0 (by rw [hzz']; simp)).2
    simpa using h
  -- `u` is the gate point of `w'` at the level `n - m`
  have hΦu : Φ u = w' - ((n - m : ℕ) : ℂ) := by
    rw [hnR, ← huR, Nat.cast_sub hmn]
    ring
  refine ⟨?_, orbit_mem_low hτF hτDf hOrb hu hΦu hgoodw' hτu hmn hlow⟩
  -- the value, by the level-independence at the level `n - m`
  have hval : Work.Pert.coordP f Df τ Φ Q w' = f^[n - m] (τ u) :=
    Work.Pert.coordP_level_eq hinjQ hAb hτF hOrb hgoodw' hu hΦu
      (fun j hj => orbit_mem_of_level hτF hτDf hOrb hu hΦu hgoodw' j hj)
  rw [hval, hτu, ← Function.iterate_add_apply, Nat.sub_add_cancel hmn]

/-- **The membership clause of `orbit`, without any reference to the pieces.**  If the whole ray
`R^[m] w, R^[m] w + 1, …, R^[m] w + n` lies in the maximal domain `Dφ`, then the Abel equation
alone turns the memberships of `φ (R^[m] w)` into `∀ i < n, f^[i] (φ (R^[m] w)) ∈ Df`. -/
theorem orbit_mem_of_ray {f φ : ℂ → ℂ} {Dφ Df : Set ℂ} {x : ℂ} {n : ℕ}
    (hAbel : ∀ z : ℂ, z ∈ Dφ → z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hray : ∀ i : ℕ, i ≤ n → x + (i : ℂ) ∈ Dφ) (hx : φ x ∈ Df) :
    ∀ i : ℕ, i < n → f^[i] (φ x) ∈ Df := by
  -- the Abel equation iterated along the ray
  have hiter : ∀ i : ℕ, i ≤ n → f^[i] (φ x) = φ (x + (i : ℂ)) := by
    intro i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have hj : j ≤ n := by omega
      have hzj : x + (j : ℂ) ∈ Dφ := hray j hj
      have hzj1 : (x + (j : ℂ)) + 1 ∈ Dφ := by
        have : x + (j : ℂ) + 1 = x + ((j + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this]; exact hray (j + 1) (by omega)
      have h1 : φ ((x + (j : ℂ)) + 1) = f (φ (x + (j : ℂ))) := (hAbel _ hzj hzj1).2
      have hcast : (x + (j : ℂ)) + 1 = x + ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [Function.iterate_succ_apply', ih hj, ← h1, hcast]
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simpa using hx
  · have hi1 : i + 1 ≤ n := by omega
    rw [hiter i (le_of_lt hi)]
    have h1 : x + (i : ℂ) ∈ Dφ := hray i (le_of_lt hi)
    have h2 : (x + (i : ℂ)) + 1 ∈ Dφ := by
      have : x + (i : ℂ) + 1 = x + ((i + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact hray (i + 1) hi1
    exact (hAbel _ h1 h2).1

/-- **The general (`m`) instance of `PertData.orbit`, reduced to the pieces' data.**  Suppose

* `φ` satisfies the Abel equation on `Dφ` (`hAbel`);
* the walk `R^j w` (`j ≤ m`) stays in `Dφ` and `R` preserves the value of `φ` there (`hinv` —
  this is the perturbed `R̃_f`-invariance `φ_f ∘ R̃_f = φ_f`, (4.3.4));
* the ray `R^m w + i` (`i ≤ n`) stays in `Dφ`;
* `w' = R^m w + n` with `n ≥ 1`.

Then the contract's conclusion holds: `f^[n] (φ w) = φ w'` and the whole orbit of `φ w` up to `n`
stays in `Df`.  Everything is the Abel equation: `φ (R^m w + j) = f^j (φ (R^m w)) = f^j (φ w)`. -/
theorem orbit_general {f φ R : ℂ → ℂ} {Dφ Df : Set ℂ} {w w' : ℂ} {m n : ℕ}
    (hAbel : ∀ z : ℂ, z ∈ Dφ → z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hwalkD : ∀ j : ℕ, j ≤ m → R^[j] w ∈ Dφ)
    (hinv : ∀ x : ℂ, x ∈ Dφ → R x ∈ Dφ → φ (R x) = φ x)
    (hray : ∀ i : ℕ, i ≤ n → R^[m] w + (i : ℂ) ∈ Dφ)
    (hx : φ (R^[m] w) ∈ Df)
    (hn : 1 ≤ n) (hw' : w' = R^[m] w + (n : ℂ)) :
    f^[n] (φ w) = φ w' ∧ ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df := by
  -- `φ` is invariant under the walk
  have hφwalk : φ (R^[m] w) = φ w := by
    have hiter : ∀ j : ℕ, j ≤ m → φ (R^[j] w) = φ w := by
      intro j hj
      induction j with
      | zero => simp
      | succ k ih =>
        have hsucc : R^[k + 1] w = R (R^[k] w) := Function.iterate_succ_apply' R k w
        rw [hsucc, hinv (R^[k] w) (hwalkD k (by omega)) (by rw [← hsucc]; exact hwalkD (k + 1) (by omega))]
        exact ih (by omega)
    exact hiter m le_rfl
  -- the memberships
  have hmem : ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df := by
    have h := orbit_mem_of_ray hAbel hray hx
    intro i hi
    rw [← hφwalk]
    exact h i hi
  refine ⟨?_, hmem⟩
  -- the value, by iterating the Abel equation along the ray
  have hray' : ∀ i : ℕ, i ≤ n → R^[m] w + (i : ℂ) ∈ Dφ := hray
  have hiter : ∀ i : ℕ, i ≤ n → f^[i] (φ (R^[m] w)) = φ (R^[m] w + (i : ℂ)) := by
    intro i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have hj : j ≤ n := by omega
      have hzj : R^[m] w + (j : ℂ) ∈ Dφ := hray' j hj
      have hzj1 : (R^[m] w + (j : ℂ)) + 1 ∈ Dφ := by
        have : R^[m] w + (j : ℂ) + 1 = R^[m] w + ((j + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this]; exact hray' (j + 1) (by omega)
      have h1 : φ ((R^[m] w + (j : ℂ)) + 1) = f (φ (R^[m] w + (j : ℂ))) :=
        (hAbel _ hzj hzj1).2
      have hcast : (R^[m] w + (j : ℂ)) + 1 = R^[m] w + ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [Function.iterate_succ_apply', ih hj, ← h1, hcast]
  rw [hw', ← hφwalk, hiter n le_rfl]

/-- **The low piece's `(INV)` from the ray and injectivity.**  `RlowPiece w + m` is the level-`0`
point `Φ (Tt α ζ_w)` of the gate, so `φ (RlowPiece w + m) = τ (Tt α ζ_w) = τ ζ_w = f^[m] (φ w)`
(`Rlow_phi_add_nat`); if the ray `RlowPiece w, …, RlowPiece w + m` lies in `Dφ`, the Abel equation
turns the left-hand side into `f^[m] (φ (RlowPiece w))`, and the injectivity of `f^[m]` on the seed
ball gives `φ (RlowPiece w) = φ w`.

This is the `m ≥ 2` input of the lower band (session 23 §4.1): it upgrades the *shifted* identity
`φ (RlowPiece w + m) = f^m (φ w)` to the honest `(INV)`. -/
theorem low_inv_of_ray {f F τ Φ Φp φ : ℂ → ℂ} {Df Q Qp' : Set ℂ} {α d : ℂ}
    {m : ℕ} {w : ℂ} {δ : ℝ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ i : ℕ, i ≤ k → F^[i] z ∈ Q) ∧ F^[k] z = z')
    (hAbel : ∀ z : ℂ, z ∈ Work.Pert.DphiP f Df τ Φ Q → z + 1 ∈ Work.Pert.DphiP f Df τ Φ Q →
      Work.Pert.coordP f Df τ Φ Q (z + 1) = f (Work.Pert.coordP f Df τ Φ Q z))
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp')
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hζQ : Work.Pert.Tt α (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Q)
    (hray : ∀ i : ℕ, i ≤ m →
      (RlowPiece f Qp' τ Φp φ m d w + (i : ℂ)) ∈ Work.Pert.DphiP f Df τ Φ Q)
    (hinjf : Set.InjOn (f^[m]) (Metric.ball (0 : ℂ) δ))
    (hmemR : Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w)
      ∈ Metric.ball (0 : ℂ) δ)
    (hmemW : φ w ∈ Metric.ball (0 : ℂ) δ) :
    Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w) = φ w := by
  -- the gate value of the shifted low piece
  have hval : Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (m : ℂ))
      = f^[m] (φ w) :=
    Rlow_phi_add_nat (c := 0) hτF hOrb hA42 hland hζQ hτT
      (by simpa using hray (m + 0) (by omega))
  -- the Abel equation iterated along the ray
  have hiter : ∀ i : ℕ, i ≤ m →
      f^[i] (Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w))
        = Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (i : ℂ)) := by
    intro i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have hj : j ≤ m := by omega
      have hzj := hray j hj
      have hzj1 : (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ)) + 1
          ∈ Work.Pert.DphiP f Df τ Φ Q := by
        have hcast : (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ)) + 1
            = RlowPiece f Qp' τ Φp φ m d w + ((j + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]; exact hray (j + 1) (by omega)
      have h1 := hAbel _ hzj hzj1
      have hcast : (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ)) + 1
          = RlowPiece f Qp' τ Φp φ m d w + ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [Function.iterate_succ_apply', ih hj, ← h1, hcast]
  have hEq : f^[m] (Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w))
      = f^[m] (φ w) := by
    rw [hiter m le_rfl, hval]
  exact hinjf hmemR hmemW hEq

/-- **The `m = 1` instance of `orbit` for a short shift.**  For `1 ≤ j < m` the value is
`Rlow_phi_translate_lt` (the minimal-level gate point of `RlowPiece w + j` is a *backward* iterate
of the crux's landing point, and `f^[m-j]` is injective on the seed ball) and the memberships are
`orbit_mem_le` (the crux's `LowClause` already covers `i < j < m`). -/
theorem orbit_one_of_level_short {f F τ Φ Φp φ : ℂ → ℂ} {Df Q Qp' : Set ℂ} {α d : ℂ}
    {m j : ℕ} {w : ℂ} {δ : ℝ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ i : ℕ, i ≤ k → F^[i] z ∈ Q) ∧ F^[k] z = z')
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp')
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hζQ : Work.Pert.Tt α (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Q)
    (hinjf : Set.InjOn (f^[m - j]) (Metric.ball (0 : ℂ) δ))
    (hj1 : 1 ≤ j) (hjm : j < m)
    (hDφ : (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ)) ∈ Work.Pert.DphiP f Df τ Φ Q)
    (hmemU : Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ))
      ∈ Metric.ball (0 : ℂ) δ)
    (hmemY : f^[j] (φ w) ∈ Metric.ball (0 : ℂ) δ)
    (hlow : ∀ i : ℕ, i ≤ m → f^[i] (φ w) ∈ Df) :
    f^[j] (φ w) = Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ)) ∧
      ∀ i : ℕ, i < j → f^[i] (φ w) ∈ Df :=
  ⟨(Rlow_phi_translate_lt hτF hOrb hA42 hland hτT hζQ hinjf hj1 hjm hDφ hmemU hmemY).symm,
    orbit_mem_le hlow (le_of_lt hjm)⟩

end

end Work.Pert.pert2v2
