import Mathlib
import Submission.Work.Peluse.Prop36SW.PeelData
import Submission.Work.Peluse.Ulower.gap_local_aux

namespace Work.Peluse.Prop36SW

/-- Every entry of the long-direction set `arithIcc (p s₀ a) ⌊γ'M₁M₂⌋` is bounded in modulus by
`N ⌈γ'D⌉` (the per-shift reach of the peel): the entry is `p s₀ a · n` with `1 ≤ n ≤ ⌊γ'M₁M₂⌋`, and
`|p s₀ a| M₁ M₂ ≤ D N` while `n ≤ γ' M₁ M₂`. -/
private theorem peelShift_natAbs_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ N D : ℕ) (A : Finset P) (γ' : ℝ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (hγ' : 0 < γ')
    (hD : ∀ a ∈ A, |p s₀.1 a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    {a : P} (ha : a ∈ A) {z : ℤ}
    (hz : z ∈ Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) :
    z.natAbs ≤ N * ⌈γ' * (D : ℝ)⌉₊ := by
  have h1 : z.natAbs ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat * (p s₀.1 a).natAbs :=
    Work.Peluse.Ulower.mem_arithIcc_le hz
  have hDz : (((p s₀.1 a).natAbs : ℤ) * (M₁ : ℤ) * (M₂ : ℤ)) ≤ (D : ℤ) * (N : ℤ) := by
    have h := hD a ha
    rw [← Int.natCast_natAbs (p s₀.1 a)] at h
    exact h
  have hDnat : (p s₀.1 a).natAbs * M₁ * M₂ ≤ D * N := by
    exact_mod_cast hDz
  have hDreal : ((p s₀.1 a).natAbs : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) ≤ (D : ℝ) * (N : ℝ) := by
    exact_mod_cast hDnat
  have hLreal : ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
    rw [Int.floor_toNat]
    exact Nat.floor_le (by positivity)
  have key : ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) * ((p s₀.1 a).natAbs : ℝ)
      ≤ ((N * ⌈γ' * (D : ℝ)⌉₊ : ℕ) : ℝ) := by
    calc ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) * ((p s₀.1 a).natAbs : ℝ)
        ≤ (γ' * (M₁ : ℝ) * (M₂ : ℝ)) * ((p s₀.1 a).natAbs : ℝ) :=
          mul_le_mul_of_nonneg_right hLreal (by positivity)
      _ = γ' * (((p s₀.1 a).natAbs : ℝ) * (M₁ : ℝ) * (M₂ : ℝ)) := by ring
      _ ≤ γ' * ((D : ℝ) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hDreal (le_of_lt hγ')
      _ = (γ' * (D : ℝ)) * (N : ℝ) := by ring
      _ ≤ ((⌈γ' * (D : ℝ)⌉₊ : ℕ) : ℝ) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
      _ = ((N * ⌈γ' * (D : ℝ)⌉₊ : ℕ) : ℝ) := by push_cast; ring
  have hfin : (z.natAbs : ℝ) ≤ ((N * ⌈γ' * (D : ℝ)⌉₊ : ℕ) : ℝ) := by
    have h1r : (z.natAbs : ℝ)
        ≤ ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) * ((p s₀.1 a).natAbs : ℝ) := by
      exact_mod_cast h1
    linarith [h1r, key]
  exact Nat.cast_le.mp hfin

theorem supportInPeelG {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ N D : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (hγ' : 0 < γ')
    (hbound : ∀ a ∈ A, p s₀.1 a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ))
    (hD : ∀ a ∈ A, |p s₀.1 a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    (hg : ∀ a ∈ A, Work.Peluse.SupportIn (g a) N)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) :
    Work.Peluse.SupportIn (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q)
      (Work.Peluse.Prop36SW.peelN N D t' γ') := by
  have hF : Work.Peluse.SupportIn (g q.1.1.1) N := hg q.1.1.1 q.1.1.2
  have hsh : ∀ j : Fin t',
      (((q.2 j).1 : ℤ), ((q.2 j).2 : ℤ)).1.natAbs ≤ N * ⌈γ' * (D : ℝ)⌉₊ ∧
      (((q.2 j).1 : ℤ), ((q.2 j).2 : ℤ)).2.natAbs ≤ N * ⌈γ' * (D : ℝ)⌉₊ := by
    intro j
    exact ⟨peelShift_natAbs_le p M₁ M₂ N D A γ' s₀ hγ' hD q.1.1.2 ((q.2 j).1).2,
      peelShift_natAbs_le p M₁ M₂ N D A γ' s₀ hγ' hD q.1.1.2 ((q.2 j).2).2⟩
  refine (Work.Peluse.Ulower.iterDelta_supportIn (k := t')
      (sh := fun j : Fin t' => (((q.2 j).1 : ℤ), ((q.2 j).2 : ℤ))) hsh hF).mono ?_
  have hN : N + t' * (N * ⌈γ' * (D : ℝ)⌉₊) ≤ Work.Peluse.Prop36SW.peelN N D t' γ' := by
    rw [Work.Peluse.Prop36SW.peelN]
    exact le_of_eq (by ring)
  exact hN

end Work.Peluse.Prop36SW
