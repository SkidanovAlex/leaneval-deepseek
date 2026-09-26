import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# Gluing a finite family of continuous two-parameter families along consecutive intervals

Given a strictly increasing sequence `u : Fin (M+1) → ℝ` of breakpoints, a continuous curve
`c : ℝ → ℝ³`, and for each `k : Fin M` a continuous family `Q k : ℝ → ℝ → ℝ³` whose values on the
two endpoints `u k.castSucc`, `u k.succ` do not depend on the first parameter and agree with `c`
there, the families `Q k` glue to a single continuous family `G : ℝ → ℝ → ℝ³` which restricts to
`Q k` on the closed interval `Icc (u k.castSucc) (u k.succ)`.  Outside the range of `u` the glued
family is extended by `c`.

The proof is an induction on the number of pieces, gluing one closed interval at a time with the
pasting lemma for two closed pieces (`ContinuousOn.union_of_isClosed`).
-/

namespace Work.Drive.EpsForm

open Set
open LeanEval.KnotTheory.PardonDistortion

/-- Auxiliary statement: gluing `n` consecutive families, with the extra information that the
glued family takes the value `c` at the last breakpoint (which the inductive construction needs). -/
private theorem glue_aux :
    ∀ n : ℕ, ∀ (u : Fin (n + 1) → ℝ), StrictMono u →
      ∀ (c : ℝ → R3), Continuous c → ∀ (Q : Fin n → ℝ → ℝ → R3),
        (∀ k, Continuous (Function.uncurry (Q k))) →
        (∀ (k : Fin n) (s : ℝ),
          Q k s (u k.castSucc) = c (u k.castSucc) ∧ Q k s (u k.succ) = c (u k.succ)) →
      ∃ G : ℝ → ℝ → R3, Continuous (Function.uncurry G) ∧
        (∀ k : Fin n, ∀ s : ℝ, ∀ t ∈ Icc (u k.castSucc) (u k.succ), G s t = Q k s t) ∧
        (∀ s : ℝ, G s (u (Fin.last n)) = c (u (Fin.last n))) := by
  intro n
  induction n with
  | zero =>
      intro u hu c hc Q hQ hmatch
      exact ⟨fun _ t => c t, hc.comp continuous_snd, fun k => Fin.elim0 k, fun s => rfl⟩
  | succ n ih =>
      intro u hu c hc Q hQ hmatch
      classical
      -- Restrict the data to the first `n` pieces.
      let u₀ : Fin (n + 1) → ℝ := fun i => u i.castSucc
      have hu₀ : StrictMono u₀ := fun i j hij => hu (Fin.castSucc_lt_castSucc_iff.mpr hij)
      have hmatch₀ : ∀ (k : Fin n) (s : ℝ),
          Q k.castSucc s (u₀ k.castSucc) = c (u₀ k.castSucc) ∧
          Q k.castSucc s (u₀ k.succ) = c (u₀ k.succ) := by
        intro k s
        have h := hmatch k.castSucc s
        exact ⟨h.1, by simpa only [Fin.succ_castSucc] using h.2⟩
      obtain ⟨G₀, hG₀cont, hG₀prop, hG₀last⟩ :=
        ih u₀ hu₀ c hc (fun k => Q k.castSucc) (fun k => hQ k.castSucc) hmatch₀
      -- Split at the last breakpoint of `u₀`, i.e. at `u₀ (Fin.last n)`.
      let S : Set (ℝ × ℝ) := {p | p.2 ≤ u₀ (Fin.last n)}
      let T : Set (ℝ × ℝ) := {p | u₀ (Fin.last n) ≤ p.2}
      let Gun : ℝ × ℝ → R3 :=
        Set.piecewise S (Function.uncurry G₀) (Function.uncurry (Q (Fin.last n)))
      have hGun_mem : ∀ p : ℝ × ℝ, p ∈ S → Gun p = Function.uncurry G₀ p :=
        fun p hp => piecewise_eq_of_mem S _ _ hp
      have hGun_notMem : ∀ p : ℝ × ℝ, p ∉ S →
          Gun p = Function.uncurry (Q (Fin.last n)) p :=
        fun p hp => piecewise_eq_of_notMem S _ _ hp
      -- `Gun` is continuous, pasting `G₀` (on `S`) and `Q (Fin.last n)` (on `T`).
      have hGun : Continuous Gun := by
        have hS : IsClosed S := isClosed_le continuous_snd continuous_const
        have hT : IsClosed T := isClosed_le continuous_const continuous_snd
        have hST : S ∪ T = univ := by
          ext p
          simp only [S, T, mem_union, mem_ofPred_eq, mem_univ, iff_true]
          exact le_total p.2 (u₀ (Fin.last n))
        have h1 : ContinuousOn Gun S :=
          hG₀cont.continuousOn.congr (piecewise_eqOn S _ _)
        have h2 : ContinuousOn Gun T := by
          refine (hQ (Fin.last n)).continuousOn.congr ?_
          intro p hp
          by_cases hpa : p.2 ≤ u₀ (Fin.last n)
          · rw [hGun_mem p hpa]
            have hpe : p.2 = u₀ (Fin.last n) := le_antisymm hpa hp
            show G₀ p.1 p.2 = Q (Fin.last n) p.1 p.2
            rw [hpe]
            exact (hG₀last p.1).trans ((hmatch (Fin.last n) p.1).1).symm
          · rw [hGun_notMem p hpa]
        have h3 : ContinuousOn Gun (S ∪ T) := h1.union_of_isClosed h2 hS hT
        rw [hST] at h3
        exact continuousOn_univ.mp h3
      refine ⟨fun s t => Gun (s, t), ?_, ?_, ?_⟩
      · have hun : Function.uncurry (fun s t => Gun (s, t)) = Gun := by
          funext p; cases p with | mk a b => rfl
        rw [hun]; exact hGun
      · intro k s t ht
        by_cases hk : (k : ℕ) = n
        · -- the last piece
          have hkeq : k = Fin.last n := Fin.ext (by rw [Fin.val_last]; exact hk)
          subst hkeq
          show Gun (s, t) = Q (Fin.last n) s t
          have ht1 : u₀ (Fin.last n) ≤ t := (mem_Icc.mp ht).1
          by_cases hpa : t ≤ u₀ (Fin.last n)
          · rw [hGun_mem (s, t) (show (s, t) ∈ S from hpa)]
            have hte : t = u₀ (Fin.last n) := le_antisymm hpa ht1
            show G₀ s t = Q (Fin.last n) s t
            rw [hte]
            exact (hG₀last s).trans ((hmatch (Fin.last n) s).1).symm
          · rw [hGun_notMem (s, t) (show (s, t) ∉ S from hpa)]
            rfl
        · -- one of the first `n` pieces: reduce to the induction hypothesis
          have hklt : (k : ℕ) < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ k.isLt) hk
          show Gun (s, t) = Q k s t
          have ht1 : t ≤ u₀ (Fin.last n) := by
            have hle : k.succ ≤ (Fin.last n).castSucc := by
              rw [Fin.le_iff_val_le_val]
              simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              omega
            exact le_trans (mem_Icc.mp ht).2 (hu.monotone hle)
          rw [hGun_mem (s, t) (show (s, t) ∈ S from ht1)]
          show G₀ s t = Q k s t
          exact hG₀prop ⟨k.val, hklt⟩ s t ht
      · -- value at the last breakpoint
        intro s
        show Gun (s, u (Fin.last (n + 1))) = c (u (Fin.last (n + 1)))
        have hlt : u (Fin.last n).castSucc < u (Fin.last (n + 1)) := by
          have h2 : (Fin.last n).castSucc < (Fin.last n).succ :=
            Fin.castSucc_lt_succ_iff.mpr le_rfl
          rw [Fin.succ_last] at h2
          exact hu h2
        have hns : ¬ (u (Fin.last (n + 1)) ≤ u₀ (Fin.last n)) := not_le.mpr hlt
        rw [hGun_notMem (s, u (Fin.last (n + 1)))
              (show (s, u (Fin.last (n + 1))) ∉ S from hns)]
        show Q (Fin.last n) s (u (Fin.last (n + 1))) = c (u (Fin.last (n + 1)))
        have h := (hmatch (Fin.last n) s).2
        rw [show (Fin.last (n+1) : Fin (n+2)) = (Fin.last n).succ from Fin.ext (by simp)]
        exact h

/-- **Gluing a finite family of continuous two-parameter families.**

Let `u 0 < u 1 < ⋯ < u M` be breakpoints, `c` a continuous curve, and `Q k` a continuous family
which is constant on the two boundary values of `c` over the `k`-th interval.  Then the `Q k` glue
to a single continuous two-parameter family `G` which agrees with `Q k` on the `k`-th interval. -/
theorem exists_glued_family {M : ℕ} (u : Fin (M+1) → ℝ) (hu : StrictMono u)
    (c : ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (hc : Continuous c)
    (Q : Fin M → ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (hQ : ∀ k, Continuous (Function.uncurry (Q k)))
    (hmatch : ∀ (k : Fin M) (s : ℝ),
      Q k s (u k.castSucc) = c (u k.castSucc) ∧ Q k s (u k.succ) = c (u k.succ)) :
    ∃ G : ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3, Continuous (Function.uncurry G) ∧
      ∀ k : Fin M, ∀ s : ℝ, ∀ t ∈ Set.Icc (u k.castSucc) (u k.succ), G s t = Q k s t := by
  obtain ⟨G, hGcont, hGprop, _⟩ := glue_aux M u hu c hc Q hQ hmatch
  exact ⟨G, hGcont, hGprop⟩

end Work.Drive.EpsForm
