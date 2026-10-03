import Mathlib
import Submission.Work.Pert.RBlock7.retPPhi

namespace Work.Pert.pert2v2

open Work.Pert _root_.MandelDim Complex Set

/-- **The value half of the Abel step, for arbitrary nonnegative shifts.**

If `X` and `X + t` both lie in the maximal domain `DphiP f Df τ Φ Q` of the gate coordinate, then
the values of `φ_f = coordP f Df τ Φ Q` at the two points are related by the `t`-th iterate of `f`:

  `coordP … Q (X + t) = f^[t] (coordP … Q X)`.

This is the quantitative form of the Abel equation `Work.Pert.coordP_abel` needed here: the
level-translation leaves the two seeds `τ (Φ⁻¹ (X - n))`, `τ (Φ⁻¹ (X + t - n'))` related by an
iterate of `F` along the gate walk supplied by `hOrb` (with the sign of the level difference
deciding which of the two is transported), and `τ ∘ F = f ∘ τ` along that walk
(`Work.Pert.tau_walk_iterate`) converts it into an iterate of `f`.  No hypothesis on the
intermediate points `X + i` is needed, and neither injectivity of `Φ` nor the `Df`-membership of
the seeds is used. -/
theorem coordP_add_nat_of_mem {f F τ Φ : ℂ → ℂ} {Q : Set ℂ} {Df : Set ℂ} {X : ℂ} {t : ℕ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hX : X ∈ Work.Pert.DphiP f Df τ Φ Q)
    (hXt : X + (t : ℂ) ∈ Work.Pert.DphiP f Df τ Φ Q) :
    Work.Pert.coordP f Df τ Φ Q (X + (t : ℂ)) = f^[t] (Work.Pert.coordP f Df τ Φ Q X) := by
  classical
  set n := Work.Pert.mIdxP f Df τ Φ Q X with hn
  set n' := Work.Pert.mIdxP f Df τ Φ Q (X + (t : ℂ)) with hn'
  have himg : ∃ z ∈ Q, Φ z = X - (n : ℂ) := by
    obtain ⟨h1, -⟩ := Work.Pert.mIdxP_spec (Work.Pert.mem_DphiP.mp hX)
    rw [← hn] at h1; exact h1
  have himg' : ∃ z ∈ Q, Φ z = (X + (t : ℂ)) - (n' : ℂ) := by
    obtain ⟨h1, -⟩ := Work.Pert.mIdxP_spec (Work.Pert.mem_DphiP.mp hXt)
    rw [← hn'] at h1; exact h1
  set ζ := Work.Pert.invOn Φ Q (X - (n : ℂ)) with hζdef
  set ζ' := Work.Pert.invOn Φ Q ((X + (t : ℂ)) - (n' : ℂ)) with hζ'def
  have hζQ : ζ ∈ Q := Work.Pert.invOn_mem himg
  have hζ'Q : ζ' ∈ Q := Work.Pert.invOn_mem himg'
  have hζΦ : Φ ζ = X - (n : ℂ) := Work.Pert.invOn_spec himg
  have hζ'Φ : Φ ζ' = (X + (t : ℂ)) - (n' : ℂ) := Work.Pert.invOn_spec himg'
  have hcX : Work.Pert.coordP f Df τ Φ Q X = f^[n] (τ ζ) := by
    rw [Work.Pert.coordP_self, ← hn]; rfl
  have hcXt : Work.Pert.coordP f Df τ Φ Q (X + (t : ℂ)) = f^[n'] (τ ζ') := by
    rw [Work.Pert.coordP_self, ← hn']; rfl
  rw [hcX, hcXt]
  rcases le_or_gt n' (n + t) with hcase | hcase
  · -- `n' ≤ n + t`: `ζ` walks up to `ζ'` in `n + t - n'` steps
    set d := n + t - n' with hd
    have hdval : ((d : ℕ) : ℂ) = (n : ℂ) + (t : ℂ) - (n' : ℂ) := by
      rw [hd, Nat.cast_sub hcase]; push_cast; ring
    have hΦk : Φ ζ' = Φ ζ + (d : ℂ) := by rw [hζ'Φ, hζΦ, hdval]; ring
    obtain ⟨hwalk, hfin⟩ := hOrb ζ hζQ ζ' hζ'Q d hΦk
    have hτζ' : τ ζ' = f^[d] (τ ζ) := by
      simpa [hfin] using Work.Pert.tau_walk_iterate hwalk hτF
    rw [hτζ', ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  · -- `n + t < n'`: `ζ'` walks up to `ζ` in `n' - n - t` steps
    set d := n' - (n + t) with hd
    have hdval : ((d : ℕ) : ℂ) = (n' : ℂ) - ((n : ℂ) + (t : ℂ)) := by
      rw [hd, Nat.cast_sub (by omega : n + t ≤ n')]; push_cast; ring
    have hΦk : Φ ζ = Φ ζ' + (d : ℂ) := by rw [hζΦ, hζ'Φ, hdval]; ring
    obtain ⟨hwalk, hfin⟩ := hOrb ζ' hζ'Q ζ hζQ d hΦk
    have hτζ : τ ζ = f^[d] (τ ζ') := by
      simpa [hfin] using Work.Pert.tau_walk_iterate hwalk hτF
    have hstep : f^[n] (τ ζ) = f^[n + d] (τ ζ') := by
      rw [hτζ, ← Function.iterate_add_apply]
    have hnd : n + d = n' - t := by omega
    rw [hstep, hnd, ← Function.iterate_add_apply]
    congr 1
    omega

/-- **The high piece at every nonnegative shift.**  The level-shifted return map
`retP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) α` preserves the coordinate value
(`Work.Pert.RBlock7.retP_phi_eq`, `t = 0`); iterating the Abel equation along the ray gives the
shifts `t ≥ 0`. -/
theorem retP_phi_shift {f F τ Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Df : Set ℂ} {w : ℂ} {t : ℕ}
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hAb : ∀ z ∈ Work.Pert.Qm Ξ α, F z ∈ Work.Pert.Qm Ξ α → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Work.Pert.Qm Ξ α, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Work.Pert.Qm Ξ α, ∀ z' ∈ Work.Pert.Qm Ξ α, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Work.Pert.Qm Ξ α) ∧ F^[k] z = z')
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hgood : Work.Pert.GoodP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w)
    (hray : ∀ i : ℕ, i ≤ t →
      Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w + (i : ℂ)
        ∈ Work.Pert.DphiP f Df τ Φ (Work.Pert.Qm Ξ α)) :
    Work.Pert.coordP f Df τ Φ (Work.Pert.Qm Ξ α)
        (Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w + (t : ℂ))
      = f^[t] (Work.Pert.coordP f Df τ Φ (Work.Pert.Qm Ξ α) w) := by
  -- The ray hypothesis supplies both endpoints of the shift lemma.
  have hX : Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w
      ∈ Work.Pert.DphiP f Df τ Φ (Work.Pert.Qm Ξ α) := by
    simpa using hray 0 (Nat.zero_le t)
  have hXt : Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w + (t : ℂ)
      ∈ Work.Pert.DphiP f Df τ Φ (Work.Pert.Qm Ξ α) := hray t le_rfl
  rw [coordP_add_nat_of_mem hτF hOrb hX hXt,
    Work.Pert.RBlock7.retP_phi_eq hinj hAb hτF hOrb hτT hgood]

end Work.Pert.pert2v2
