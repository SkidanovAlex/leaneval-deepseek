import Mathlib

namespace Work.IonescuWainger

/-- **Summation over the sublattice `Qℤ` of `ℤ`**: a series whose terms vanish off the multiples
of `Q > 0` is the series of the sampled terms `m ↦ f (Q m)`.  This is the reindexing step that
identifies Tao's `p = ∞` weighted sums (which are supported on the annihilator `Q_Aℤ`, see
`kernel_arcSymbol_torsion`) with lattice sums over `ℤ`. -/
theorem tsum_ite_dvd_eq_tsum_mul {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T2Space E]
    {Q : ℕ} (hQ : 0 < Q) (f : ℤ → E) :
    (∑' n : ℤ, if (Q : ℤ) ∣ n then f n else 0) = ∑' m : ℤ, f ((Q : ℤ) * m) := by
  have hQZ : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  let s : Set ℤ := {n | (Q : ℤ) ∣ n}
  have hL : (∑' n : ℤ, if (Q : ℤ) ∣ n then f n else 0) = ∑' x : s, f ↑x := by
    rw [tsum_subtype s f]
    apply tsum_congr
    intro n
    rw [Set.indicator_apply]
    rfl
  rw [hL]
  let e : ℤ ≃ s :=
    { toFun := fun m => ⟨(Q : ℤ) * m, ⟨m, rfl⟩⟩
      invFun := fun x => (x : ℤ) / (Q : ℤ)
      left_inv := fun m => Int.mul_ediv_cancel_left m hQZ
      right_inv := fun x => by
        obtain ⟨n, hn⟩ := x
        simp only [Subtype.mk.injEq]
        exact Int.mul_ediv_cancel' hn }
  rw [← Equiv.tsum_eq e (fun x : s => f ↑x)]
  apply tsum_congr
  intro m
  rfl

end Work.IonescuWainger
