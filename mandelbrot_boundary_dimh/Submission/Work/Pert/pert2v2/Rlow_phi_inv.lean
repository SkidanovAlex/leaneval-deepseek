import Mathlib
import Submission.Work.Pert.pert2v2.RBlockDefs
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.RBlock3
import Submission.Work.Pert.RBlock5.Rlow_seed_phi_eq
import Submission.Work.Pert.coordP_level_eq

/-!
# `Work.Pert.pert2v2.Rlow_phi_inv` — the low piece preserves the coordinate value

`RlowPiece f Qp' τ Φp φ m d w = Φp (invOn τ Qp' (f^[m] (φ w))) - m + d` is the low piece of the
lifted return map `R̃_f` (`Work.Pert.pert2v2.RBlockDefs`).  If `w` is a point whose coordinate value
`φ w = coordP f Df τ Φ Q w` equals `f^[E] (τ ς)` for a gate point `ς` whose `F`-walk up to level
`E + m` stays in the gate `Qp Ξ α` (the "gate walk" hypothesis `hgw`) and whose `(E+m)`-th iterate
lies in the subgate `Qp'` where `τ` is injective, then the low piece *preserves* the coordinate
value:

  `φ_f (R̃_f w) = φ_f w`.

The proof reduces the claim to the level bookkeeping of the coordinate:

* `φ w = f^[E] (τ ς)`, so `f^[m] (φ w) = τ (F^[E+m] ς)` (`hτF` is global), hence the chosen preimage
  in the gate is `F^[E+m] ς` (`hinjτ`, `hFm`);
* the (A.4.2) overlap relation at the gate point `F^[E+m] ς` identifies
  `Φp (F^[E+m] ς) + d = Φ (F^[E+m] (Tt α ς))`, and the iterated Abel equation along the walk
  `F^[j] (Tt α ς) = Tt α (F^[j] ς) ∈ Q` (`hTtF`, `hTtQ`, `hgw`) gives
  `Φ (F^[E+m] (Tt α ς)) = Φ (Tt α ς) + (E+m)`.  Hence `R̃_f w = Φ (Tt α ς) + E`.

So `R̃_f w` has the *level* `E` with gate point `Tt α ς`, and the value of the coordinate there is
`f^[E] (τ (Tt α ς)) = f^[E] (τ ς) = φ w` (`hτT`).  The level-comparison lemma
`coordP_eq_iterate_of_level` below discharges the (surprisingly subtle) point that `coordP` is
computed at the *minimal* level: if some legal level is `≥ E` then the level `E` is itself legal
(`hOrb` converts the walk), and if the minimal level is `≤ E` then `hOrb` identifies its gate point
as an `F`-iterate of `Tt α ς`, so `τ` of it is an `f`-iterate of `τ (Tt α ς)`.
-/

namespace Work.Pert.pert2v2

open Work.Pert

/-- **The coordinate at a level.**  If `U` is in the maximal domain `DphiP f Df τ Φ Q` and `ζ ∈ Q`
is a gate point at level `E` of `U` (`Φ ζ = U - E`), then the coordinate value of `U` is
`f^[E] (τ ζ)` — computed at the *minimal* level of `U`, but independent of the choice of the legal
level.

The `Df`-condition of `DphiP` is only needed to be able to *speak* about the minimal level; the
value comparison uses `hOrb` alone: either the minimal level `n₀ ≤ E`, and then `hOrb` exhibits the
minimal level's gate point as `F^[E-n₀] ζ`, so `τ` of it is `f^[E-n₀] (τ ζ)`; or `n₀ > E`, and then
`hOrb` together with the orbit condition at the minimal level shows that `(E, ζ)` is itself an
admissible level, contradicting minimality. -/
lemma coordP_eq_iterate_of_level {f F τ Φ : ℂ → ℂ} {Df Q : Set ℂ} {U ζ : ℂ} {E : ℕ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hU : U ∈ Work.Pert.DphiP f Df τ Φ Q) (hζQ : ζ ∈ Q)
    (hΦ : Φ ζ = U - (E : ℂ)) :
    Work.Pert.coordP f Df τ Φ Q U = f^[E] (τ ζ) := by
  -- `hOrb` at `k = 0` says that `Φ` is injective on `Q`.
  have hinj : Set.InjOn Φ Q := by
    intro z hz z' hz' hzz'
    have h := (hOrb z hz z' hz' 0 (by rw [hzz']; simp)).2
    simpa using h
  obtain ⟨hzm, hzmorb⟩ := Work.Pert.mIdxP_spec hU
  obtain ⟨ζm, hζmQ, hζmΦ⟩ := hzm
  set n₀ : ℕ := Work.Pert.mIdxP f Df τ Φ Q U with hmn
  have hseedm : Work.Pert.seedP τ Φ Q (U - (n₀ : ℂ)) = τ ζm :=
    Work.Pert.seedP_eq_of_mem' hinj ⟨ζm, hζmQ, hζmΦ⟩ hζmQ hζmΦ
  rcases le_or_gt n₀ E with hle | hlt
  · -- the minimal level is below `E`: `ζm` is an `F`-iterate of `ζ`
    have hshift : Φ ζm = Φ ζ + ((E - n₀ : ℕ) : ℂ) := by
      rw [hζmΦ, hΦ, Nat.cast_sub hle]; ring
    have hτ : τ ζm = f^[E - n₀] (τ ζ) :=
      Work.Pert.tau_eq_iterate_of_shift hτF hOrb hζQ hζmQ hshift
    rw [Work.Pert.coordP_self, ← hmn, hseedm, hτ, ← Function.iterate_add_apply,
      Nat.add_sub_of_le hle]
  · -- the minimal level is above `E`: then `(E, ζ)` is itself an admissible level
    exfalso
    have hshift : Φ ζ = Φ ζm + ((n₀ - E : ℕ) : ℂ) := by
      rw [hζmΦ, hΦ, Nat.cast_sub (le_of_lt hlt)]; ring
    have hτ : τ ζ = f^[n₀ - E] (τ ζm) :=
      Work.Pert.tau_eq_iterate_of_shift hτF hOrb hζmQ hζQ hshift
    have hseedE : Work.Pert.seedP τ Φ Q (U - (E : ℂ)) = τ ζ :=
      Work.Pert.seedP_eq_of_mem' hinj ⟨ζ, hζQ, hΦ⟩ hζQ hΦ
    refine absurd (Work.Pert.mIdxP_le hU ?_) (not_le.mpr hlt)
    refine ⟨⟨ζ, hζQ, hΦ⟩, fun j hj => ?_⟩
    rw [hseedE, hτ, ← Function.iterate_add_apply, ← hseedm]
    exact hzmorb _ (by omega)

theorem Rlow_phi_inv {f F τ Φ Φp : ℂ → ℂ} {Df Q Qp' : Set ℂ} {Ξ : ℝ} {α d : ℂ} {m E : ℕ}
    {w ς : ℂ}
    (hinjτ : Set.InjOn τ Qp')
    (hQp'sub : Qp' ⊆ Work.Pert.Qp Ξ α)
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hτF : ∀ x : ℂ, τ (F x) = f (τ x))
    (hTtF : ∀ x : ℂ, Work.Pert.Tt α (F x) = F (Work.Pert.Tt α x))
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hTtQ : ∀ z ∈ Work.Pert.Qp Ξ α, Work.Pert.Tt α z ∈ Q)
    (hΦAbel : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hgw : ∀ i : ℕ, i ≤ E + m → F^[i] ς ∈ Work.Pert.Qp Ξ α)
    (hFm : F^[E + m] ς ∈ Qp')
    (hφw : Work.Pert.coordP f Df τ Φ Q w = f^[E] (τ ς))
    (hDφR : Work.Pert.DphiP f Df τ Φ Q
      (Work.Pert.pert2v2.RlowPiece f Qp' τ Φp (Work.Pert.coordP f Df τ Φ Q) m d w)) :
    Work.Pert.coordP f Df τ Φ Q
        (Work.Pert.pert2v2.RlowPiece f Qp' τ Φp (Work.Pert.coordP f Df τ Φ Q) m d w)
      = Work.Pert.coordP f Df τ Φ Q w := by
  -- `τ` and `Tt α` intertwine the iterates of `F` with those of `f` and with themselves.
  have hτiter : ∀ (k : ℕ) (x : ℂ), f^[k] (τ x) = τ (F^[k] x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply' f j (τ x), ih x, ← hτF (F^[j] x),
        Function.iterate_succ_apply' F j x]
  have hTtiter : ∀ (k : ℕ) (x : ℂ), Work.Pert.Tt α (F^[k] x) = F^[k] (Work.Pert.Tt α x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply' F j x, hTtF (F^[j] x), ih x,
        Function.iterate_succ_apply' F j (Work.Pert.Tt α x)]
  -- **Step 1.** The gate point of the `m`-th iterate of `φ w` is `F^[E+m] ς`.
  have hfm : f^[m] ((Work.Pert.coordP f Df τ Φ Q) w) = τ (F^[E + m] ς) := by
    rw [hφw, ← Function.iterate_add_apply, Nat.add_comm m E]
    exact hτiter (E + m) ς
  have hζ : Work.Pert.invOn τ Qp'
      (f^[m] ((Work.Pert.coordP f Df τ Φ Q) w)) = F^[E + m] ς := by
    rw [hfm]
    exact Work.Pert.invOn_eq hinjτ ⟨F^[E + m] ς, hFm, rfl⟩ hFm rfl
  set U : ℂ := Work.Pert.pert2v2.RlowPiece f Qp' τ Φp (Work.Pert.coordP f Df τ Φ Q) m d w
    with hUdef
  have h1 : U = Φp (F^[E + m] ς) - (m : ℂ) + d := by
    rw [hUdef]
    simp only [Work.Pert.pert2v2.RlowPiece, Work.Pert.Rlow, hζ, Int.cast_zero]
    ring
  -- **Step 2.** The (A.4.2) relation at the gate point.
  have h2 : Φ (F^[E + m] (Work.Pert.Tt α ς)) = Φp (F^[E + m] ς) + d := by
    rw [← hTtiter (E + m) ς]
    exact hA42 (F^[E + m] ς) hFm
  -- **Step 3.** The Abel walk in `Q`.
  have hwalkTt : ∀ j : ℕ, j ≤ E + m → F^[j] (Work.Pert.Tt α ς) ∈ Q := by
    intro j hj
    rw [← hTtiter j ς]
    exact hTtQ _ (hgw j hj)
  have h3 : Φ (F^[E + m] (Work.Pert.Tt α ς)) = Φ (Work.Pert.Tt α ς) + ((E + m : ℕ) : ℂ) :=
    Work.Pert.abel_iter hwalkTt hΦAbel
  -- **Step 4.** `R̃_f w` is the level-`E` point above `Tt α ς`.
  have hkey : U = Φ (F^[E + m] (Work.Pert.Tt α ς)) - (m : ℂ) := by
    rw [h1, h2]
    ring
  have h4 : U = Φ (Work.Pert.Tt α ς) + (E : ℂ) := by
    rw [hkey, h3]
    push_cast
    ring
  have hςQp : ς ∈ Work.Pert.Qp Ξ α := by simpa using hgw 0 (Nat.zero_le (E + m))
  have hζQ : Work.Pert.Tt α ς ∈ Q := hTtQ ς hςQp
  have hΦeq : Φ (Work.Pert.Tt α ς) = U - (E : ℂ) := by rw [h4]; ring
  -- **Step 5.** Evaluate the coordinate at `U` and identify the value.
  have hcoord : Work.Pert.coordP f Df τ Φ Q U = f^[E] (τ (Work.Pert.Tt α ς)) :=
    coordP_eq_iterate_of_level (Q := Q) (E := E) (ζ := Work.Pert.Tt α ς)
      (fun z _ => hτF z) hOrb hDφR hζQ hΦeq
  rw [hcoord, hτT ς]
  exact hφw.symm

end Work.Pert.pert2v2
