import Mathlib
import Submission.Work.Pert.pert2v2.Rlow_gate_value
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Gates

/-!
# `Work.Pert.pert2v2.level_translate` — the low band's orbit step, via the *level*, not the walk

Session 20/21 attacked the low band through the **coordinate identity** `φ (R̃ w) = φ w` (`(INV)`)
with the gate-walk hypothesis `(GW)`, and stalled because at low heights the gate point `ς` of `w`
is at `|Re ς| ≈ Ξ' ≫ |Im ς|`, hence never in the waist, so neither `Tt α ς ∈ Qm` nor a walk in `Qp`
is available.

The present file records the *correct* low-band mechanism, which needs **no walk at all**.  The
whole content of the contract's `orbit` at a low point `w` is the *value* statement

  `φ (R̃ w + j) = f^j (φ w)`   (the instance `w' = R̃ w + j`, `j ≥ 1`),

and this follows from the level bookkeeping of `coordP` alone:

* the crux gives `ζ := invOn τ Qp' (f^[m] (φ w)) ∈ Qp'` with `τ ζ = f^[m] (φ w)`
  (`crux_limit_v3`/`crux_positions`), whence `u := Tt α ζ ∈ Qm` (`Qp' ⊆ Qp` and `Tt_mem_Qm_iff`);
* `RlowPiece w = Φ u - m` (`pert2v2.RlowPiece_eq_gateValue`, proved);
* so with `j = m + c` (`c ≥ 0`), the point `U := RlowPiece w + j` satisfies
  `U = Φ u + c`, i.e. `u ∈ Q` is a gate point of `U` **at the level `c`**;
* `coordP_eq_iterate_of_level` (proved) then gives, for *any* `U ∈ DphiP`

  `φ U = f^c (τ u) = f^c (τ ζ) = f^c (f^[m] (φ w)) = f^[m + c] (φ w)`.

So the `j ≥ m` instances of `orbit` are immediate — no walk, no `(GW)`, no `(INV)`; and `(INV)`
itself is *not* needed anywhere.  The two remaining quantitative inputs of the low band are
(a) `j ≥ m` for every instance satisfying the angle condition (the (A.4.5′)-type estimate) and
(b) the analogous chain for the `m ≥ 2` instances (where the walk from `R̃ w` runs through the high
piece), both stated separately.
-/

namespace Work.Pert.pert2v2

open Work.Pert MandelDim

/-- **The level translation.**  If `u ∈ Q` and `U ∈ DphiP f Df τ Φ Q` with `Φ u = U - c`, then
`φ U = f^c (τ u)`.  This is `coordP_eq_iterate_of_level` with the level `c` *made explicit* — the
point is that `coordP` is computed at the *minimal* level, so the lemma needs no minimality and no
walk: the level `c` is admissible by construction. -/
theorem coordP_of_level_eq (f F τ Φ : ℂ → ℂ) (Df Q : Set ℂ) {U u : ℂ} {c : ℕ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ i : ℕ, i ≤ k → F^[i] z ∈ Q) ∧ F^[k] z = z')
    (hU : U ∈ Work.Pert.DphiP f Df τ Φ Q) (hu : u ∈ Q) (hΦ : Φ u = U - (c : ℂ)) :
    Work.Pert.coordP f Df τ Φ Q U = f^[c] (τ u) :=
  coordP_eq_iterate_of_level hτF hOrb hU hu hΦ

/-- **The low band's orbit step.**  With the crux's data for the low piece `RlowPiece` (the
(A.4.2) relation on the subgate `Qp'`, the landing `τ ζ = f^[m] (φ w)` with `ζ ∈ Qp'` whose deck
translate `Tt α ζ` lies in the gate `Q`), the point `R̃ w + j` at the shift `j = m + c` (`c ≥ 0`)
has coordinate value `f^[m + c] (φ w)`:

  `φ (RlowPiece w + (m + c)) = f^[m + c] (φ w)`.

This is the "`j ≥ m`" half of the low-band `orbit` field: the shift `j` of the contract's instance
is `m + c`, and the extra level `c` (which is *not* a level of `φ`, but of the gate `Q`) absorbs
the remaining `m + c` iterates through `τ (Tt α ζ) = τ ζ = f^[m] (φ w)`. -/
theorem Rlow_phi_add_nat {f F τ Φ Φp φ : ℂ → ℂ} {Df Q Qp' : Set ℂ} {α d : ℂ} {m c : ℕ} {w : ℂ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ i : ℕ, i ≤ k → F^[i] z ∈ Q) ∧ F^[k] z = z')
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp')
    (hζQ : Work.Pert.Tt α (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Q)
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hDφR : (RlowPiece f Qp' τ Φp φ m d w + ((m + c : ℕ) : ℂ))
      ∈ Work.Pert.DphiP f Df τ Φ Q) :
    Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + ((m + c : ℕ) : ℂ))
      = f^[m + c] (φ w) := by
  set ζ : ℂ := Work.Pert.invOn τ Qp' (f^[m] (φ w)) with hζdef
  have hτζ : τ ζ = f^[m] (φ w) := Work.Pert.invOn_spec hland
  set u : ℂ := Work.Pert.Tt α ζ with hudef
  -- the crux formula is a gate value minus the level `m`
  have hR : RlowPiece f Qp' τ Φp φ m d w = Φ u - (m : ℂ) := by
    rw [hudef, hζdef]
    exact RlowPiece_eq_gateValue hA42 hland
  -- the level of `R̃ w + (m + c)` is `c`, with gate point `u`
  have hΦu : Φ u = (RlowPiece f Qp' τ Φp φ m d w + ((m + c : ℕ) : ℂ)) - (c : ℂ) := by
    rw [hR]
    push_cast
    ring
  rw [coordP_eq_iterate_of_level hτF hOrb hDφR hζQ hΦu, hudef, hτT, hτζ,
    Nat.add_comm m c, Function.iterate_add_apply]

end Work.Pert.pert2v2
