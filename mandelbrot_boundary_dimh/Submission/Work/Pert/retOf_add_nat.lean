import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.Qm_Qp

namespace Work.Pert

/-- **`T`-equivariance of the lifted return map along integer levels.**

If `Φ` is a Fatou coordinate of `F` on the lower gate `Qm Ξ α`, `F` commutes with the deck
translation `Tt α = w ↦ w - 1/α`, and `z = invOn Φ (Qm Ξ α) w`, `z' = invOn Φ (Qm Ξ α) (w + n)`
are the two chosen preimages of `w` resp. `w + n`, then `hOrb` identifies `z' = F^[n] z` and
keeps the whole walk `F^[j] z` (`j ≤ n`) inside the gate; the auxiliary hypothesis `hwalk` puts
that walk inside the overlap `Qm ∩ Qp`, on which `hTQp` transports it back by the deck translation,
so that `abel_iter` applies to `Tt α z`:

`Φ (Tt α (F^[n] z)) = Φ (F^[n] (Tt α z)) = Φ (Tt α z) + n`. -/
theorem retOf_add_nat {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ}
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hcomm : ∀ w : ℂ, F (Work.Pert.Tt α w) = Work.Pert.Tt α (F w))
    (hOrb : ∀ z ∈ Work.Pert.Qm Ξ α, ∀ z' ∈ Work.Pert.Qm Ξ α, ∀ k : ℕ,
      Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Work.Pert.Qm Ξ α) ∧ F^[k] z = z')
    (hTQp : ∀ z ∈ Work.Pert.Qm Ξ α, z ∈ Work.Pert.Qp Ξ α → Work.Pert.Tt α z ∈ Work.Pert.Qm Ξ α)
    {w : ℂ} (hw : w ∈ Φ '' (Work.Pert.Qm Ξ α))
    {n : ℕ} (hwn : w + (n : ℂ) ∈ Φ '' (Work.Pert.Qm Ξ α))
    (hwalk : ∀ j : ℕ, j ≤ n → F^[j] (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w)
      ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) :
    Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α (w + (n : ℂ))
      = Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α w + (n : ℂ) := by
  classical
  have hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α) := hΦ.2.1
  have hab : ∀ z ∈ Work.Pert.Qm Ξ α, F z ∈ Work.Pert.Qm Ξ α → Φ (F z) = Φ z + 1 := hΦ.2.2
  -- the two chosen preimages (keep a copy of `hwn`: `obtain` clears it)
  have hwn' : w + (n : ℂ) ∈ Φ '' (Work.Pert.Qm Ξ α) := hwn
  obtain ⟨z', hz'Q, hz'Φ⟩ := hwn
  set z : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w with hzdef
  have hzQ : z ∈ Work.Pert.Qm Ξ α := by rw [hzdef]; exact Work.Pert.invOn_mem hw
  have hzΦ : Φ z = w := by rw [hzdef]; exact Work.Pert.invOn_spec hw
  -- `hOrb` identifies `z'` with `F^[n] z` and keeps the walk in the gate
  have hOrb' := hOrb z hzQ z' hz'Q n (by rw [hz'Φ, hzΦ])
  have hwalkQ : ∀ j : ℕ, j ≤ n → F^[j] z ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    fun j hj => by simpa [hzdef] using hwalk j hj
  -- commutation of `Tt α` with the iterates of `F`
  have hc : Function.Commute (Work.Pert.Tt α) F := fun x => (hcomm x).symm
  have hiter : ∀ j : ℕ, Work.Pert.Tt α (F^[j] z) = F^[j] (Work.Pert.Tt α z) :=
    fun j => (hc.iterate_right j) z
  -- the transported walk stays inside `Qm`
  have hwalkT : ∀ j : ℕ, j ≤ n → F^[j] (Work.Pert.Tt α z) ∈ Work.Pert.Qm Ξ α := by
    intro j hj
    have h1 := hwalkQ j hj
    have h2 : Work.Pert.Tt α (F^[j] z) ∈ Work.Pert.Qm Ξ α := hTQp _ h1.1 h1.2
    rwa [hiter j] at h2
  -- iterated Abel equation along the transported walk
  have hkey : Φ (F^[n] (Work.Pert.Tt α z)) = Φ (Work.Pert.Tt α z) + (n : ℂ) :=
    abel_iter hwalkT hab
  have hinv : Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) (w + (n : ℂ)) = F^[n] z :=
    Work.Pert.invOn_eq hinj hwn' (hOrb'.1 n le_rfl) (by rw [hOrb'.2, hz'Φ])
  have hret1 : Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α (w + (n : ℂ))
      = Φ (Work.Pert.Tt α (F^[n] z)) := by
    rw [Work.Pert.retOf, hinv]
  have hret0 : Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α w = Φ (Work.Pert.Tt α z) := by
    rw [Work.Pert.retOf, hzdef]
  rw [hret1, hret0, hiter n, hkey]

end Work.Pert
