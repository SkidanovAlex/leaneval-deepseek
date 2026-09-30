import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-- Telescoping sum for an antitone `ℕ`-valued function: the sum of successive decreases
equals the total decrease. -/
private lemma sum_range_antitone (f : ℕ → ℕ) (h : ∀ t, f (t+1) ≤ f t) (n : ℕ) :
    ∑ t ∈ Finset.range n, (f t - f (t+1)) = f 0 - f n := by
  have hanti : ∀ n, f n ≤ f 0 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ k ih => exact le_trans (h k) ih
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : f (n+1) ≤ f n := h n
    have h2 : f n ≤ f 0 := hanti n
    omega

theorem convTelescope (𝕜 : Type) [Field 𝕜] {V : Type} [AddCommGroup V] [Module 𝕜 V]
    [Module.Finite 𝕜 V] (A : ℕ → Submodule 𝕜 V) (hmono : ∀ t : ℕ, A (t+1) ≤ A t) (m : ℕ)
    (hbot : A (m+1) = ⊥) :
    (∑ t ∈ Finset.range (m+1), Module.finrank 𝕜 (↥(A t) ⧸ Submodule.comap (A t).subtype (A (t+1))))
      = Module.finrank 𝕜 ↥(A 0) := by
  set f : ℕ → ℕ := fun t => Module.finrank 𝕜 ↥(A t) with hf
  have hmono_f : ∀ t, f (t+1) ≤ f t := by
    intro t
    rw [hf]
    exact Submodule.finrank_mono (hmono t)
  have hstep : ∀ t : ℕ,
      Module.finrank 𝕜 (↥(A t) ⧸ Submodule.comap (A t).subtype (A (t+1))) = f t - f (t+1) := by
    intro t
    rw [hf]
    rw [Submodule.finrank_quotient (N := Submodule.comap (A t).subtype (A (t+1)))]
    congr 1
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hmono t))
  have hcongr : (∑ t ∈ Finset.range (m+1),
        Module.finrank 𝕜 (↥(A t) ⧸ Submodule.comap (A t).subtype (A (t+1))))
      = ∑ t ∈ Finset.range (m+1), (f t - f (t+1)) :=
    Finset.sum_congr rfl (fun t _ => hstep t)
  have hbotf : f (m+1) = 0 := by
    rw [hf]
    change Module.finrank 𝕜 ↥(A (m+1)) = 0
    rw [hbot]
    simp
  rw [hcongr, sum_range_antitone f hmono_f (m+1), hbotf, Nat.sub_zero, hf]

end Work.Pi6.MSS
