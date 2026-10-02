import Mathlib
import Submission.Work.Kunneth.EzawCycleProof
import Submission.Work.Kunneth.ezaw_model_acyclic
import Submission.Work.Kunneth.EzawCycle
import Submission.Work.Kunneth.Em_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Existence of the acyclic-models chain `W` for `ezMap ≫ awMap ≃ 𝟙`

The recursion of the acyclic-models construction for the second Eilenberg–Zilber chain homotopy
asks for model chains `W p q ∈ (tMod p q).X (p+q+1)` satisfying
`d (W p q) = dfc W p q`, where `dfc W p q` depends only on the values of `W` on the models of
total degree `p+q-1`.  This file builds such a family by strong recursion on the total degree: at
level `n+1` the defect `dfc F p q` of the level-`n` data is a cycle (`dfc_cycle`), and a filler is
produced by the acyclicity of the model (`ezaw_model_acyclic`).

* `dfc_congr_lt` — the defect at total degree `≤ m` depends only on the values of `W` at total
  degree `< m`;
* `Wfill`, `Wfill_spec` — the filler of the defect at level `n+1` from level-`n` data;
* `Wdata` — the level recursion, a family of functions with their recursion equations;
* `Wz`, `Wz_spec` — the assembled family and its recursion equation;
* `ezaw_W_exists` — the existence statement consumed by `ezaw_homotopy_of_W`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The defect depends only on the values one level below**: if `W` and `W'` agree on all pairs
of total degree `< m` then `dfc W` and `dfc W'` agree on all pairs of total degree `≤ m`. -/
lemma dfc_congr_lt (W W' : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (m : ℕ)
    (h : ∀ p q, p + q < m → W p q = W' p q) :
    ∀ p q, p + q ≤ m → dfc W p q = dfc W' p q := by
  intro p q hpq
  rcases p with _ | p' <;> rcases q with _ | q'
  · rw [show dfc W 0 0 = Em 0 0 from rfl, show dfc W' 0 0 = Em 0 0 from rfl]
  · rw [dfc_eq_dfc2 W 0 (q' + 1), dfc_eq_dfc2 W' 0 (q' + 1),
      show dfc2 W 0 (q' + 1) = Em 0 (q' + 1) - psiTsum W 0 q' from rfl,
      show dfc2 W' 0 (q' + 1) = Em 0 (q' + 1) - psiTsum W' 0 q' from rfl,
      show psiTsum W 0 q' = psiTsum W' 0 q' from by
        rw [show psiTsum W 0 q' = (psiSum 0 q').f (0 + q' + 1) (W 0 q') from rfl,
          show psiTsum W' 0 q' = (psiSum 0 q').f (0 + q' + 1) (W' 0 q') from rfl,
          h 0 q' (by omega)]]
  · rw [dfc_eq_dfc2 W (p' + 1) 0, dfc_eq_dfc2 W' (p' + 1) 0,
      show dfc2 W (p' + 1) 0 = Em (p' + 1) 0 - phiTsum W p' 0 from rfl,
      show dfc2 W' (p' + 1) 0 = Em (p' + 1) 0 - phiTsum W' p' 0 from rfl,
      show phiTsum W p' 0 = phiTsum W' p' 0 from by
        rw [show phiTsum W p' 0 = dcast (p' + 1) 0 (Nat.add_right_comm p' 1 0).symm
              ((phiSum p' 0).f (p' + 0 + 1) (W p' 0)) from rfl,
          show phiTsum W' p' 0 = dcast (p' + 1) 0 (Nat.add_right_comm p' 1 0).symm
              ((phiSum p' 0).f (p' + 0 + 1) (W' p' 0)) from rfl,
          h p' 0 (by omega)]]
  · rw [dfc_eq_dfc2 W (p' + 1) (q' + 1), dfc_eq_dfc2 W' (p' + 1) (q' + 1),
      show dfc2 W (p' + 1) (q' + 1) = Em (p' + 1) (q' + 1) - phiTsum W p' (q' + 1)
        - (-1 : ℤ) ^ (p' + 1) • psiTsum W (p' + 1) q' from rfl,
      show dfc2 W' (p' + 1) (q' + 1) = Em (p' + 1) (q' + 1) - phiTsum W' p' (q' + 1)
        - (-1 : ℤ) ^ (p' + 1) • psiTsum W' (p' + 1) q' from rfl,
      show phiTsum W p' (q' + 1) = phiTsum W' p' (q' + 1) from by
        rw [show phiTsum W p' (q' + 1) = dcast (p' + 1) (q' + 1)
              (Nat.add_right_comm p' 1 (q' + 1)).symm
              ((phiSum p' (q' + 1)).f (p' + (q' + 1) + 1) (W p' (q' + 1))) from rfl,
          show phiTsum W' p' (q' + 1) = dcast (p' + 1) (q' + 1)
              (Nat.add_right_comm p' 1 (q' + 1)).symm
              ((phiSum p' (q' + 1)).f (p' + (q' + 1) + 1) (W' p' (q' + 1))) from rfl,
          h p' (q' + 1) (by omega)],
      show psiTsum W (p' + 1) q' = psiTsum W' (p' + 1) q' from by
        rw [show psiTsum W (p' + 1) q' = (psiSum (p' + 1) q').f ((p' + 1) + q' + 1)
              (W (p' + 1) q') from rfl,
          show psiTsum W' (p' + 1) q' = (psiSum (p' + 1) q').f ((p' + 1) + q' + 1)
              (W' (p' + 1) q') from rfl,
          h (p' + 1) q' (by omega)]]

/-- The filler of the defect at level `n+1`, from data satisfying the recursion equation at all
levels `≤ n`: the cycle `dfc F p q` is a boundary because the model `tMod p q` is acyclic in
positive degree. -/
noncomputable def Wfill (F : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (n : ℕ)
    (hF : ∀ p q, p + q ≤ n → (tMod p q).d (p + q + 1) (p + q) (F p q) = dfc F p q)
    (p q : ℕ) (h1 : 1 ≤ p + q) (h2 : p + q ≤ n + 1) : ↥((tMod p q).X (p + q + 1)) :=
  Classical.choose (ezaw_model_acyclic p q (p + q) h1 (dfc F p q)
    (dfc_cycle F p q h1 (fun a b hab => hF a b (by omega))))

/-- The defining property of `Wfill`. -/
lemma Wfill_spec (F : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (n : ℕ)
    (hF : ∀ p q, p + q ≤ n → (tMod p q).d (p + q + 1) (p + q) (F p q) = dfc F p q)
    (p q : ℕ) (h1 : 1 ≤ p + q) (h2 : p + q ≤ n + 1) :
    (tMod p q).d (p + q + 1) (p + q) (Wfill F n hF p q h1 h2) = dfc F p q :=
  Classical.choose_spec (ezaw_model_acyclic p q (p + q) h1 (dfc F p q)
    (dfc_cycle F p q h1 (fun a b hab => hF a b (by omega))))

/-- **The level recursion**: a function family whose values on all pairs of total degree `≤ n`
satisfy the recursion equation. -/
noncomputable def Wdata (n : ℕ) : {F : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)) //
    ∀ p q, p + q ≤ n → (tMod p q).d (p + q + 1) (p + q) (F p q) = dfc F p q} :=
  match n with
  | 0 => ⟨0, by
      intro p q hpq
      obtain rfl : p = 0 := by omega
      obtain rfl : q = 0 := by omega
      rw [show dfc (0 : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) 0 0 = Em 0 0 from rfl,
        Em_zero]
      change (ModuleCat.Hom.hom ((tMod 0 0).d (0 + 0 + 1) (0 + 0)))
        (0 : ↥((tMod 0 0).X (0 + 0 + 1))) = 0
      exact map_zero _⟩
  | (n + 1) => by
      obtain ⟨F, hF⟩ := Wdata n
      let F' : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)) := fun p q =>
        if h : p + q ≤ n then F p q
        else if h2 : p + q ≤ n + 1 then Wfill F n hF p q (by omega) h2 else 0
      refine ⟨F', ?_⟩
      have hle : ∀ (a b : ℕ) (hab : a + b ≤ n), F' a b = F a b := by
        intro a b hab
        show (if h : a + b ≤ n then F a b
          else if h2 : a + b ≤ n + 1 then Wfill F n hF a b (by omega) h2 else 0) = F a b
        rw [dif_pos hab]
      have hstep : ∀ (a b : ℕ) (hab : a + b = n + 1),
          F' a b = Wfill F n hF a b (by omega) (by omega) := by
        intro a b hab
        show (if h : a + b ≤ n then F a b
          else if h2 : a + b ≤ n + 1 then Wfill F n hF a b (by omega) h2 else 0)
          = Wfill F n hF a b (by omega) (by omega)
        rw [dif_neg (by omega), dif_pos (by omega)]
      intro p q hpq
      by_cases h : p + q ≤ n
      · rw [hle p q h, hF p q h]
        exact dfc_congr_lt F F' (n + 1) (fun a b hab => (hle a b (by omega)).symm) p q (by omega)
      · have h2 : p + q = n + 1 := by omega
        rw [hstep p q h2, Wfill_spec]
        exact dfc_congr_lt F F' (n + 1) (fun a b hab => (hle a b (by omega)).symm) p q (by omega)

/-- The level-`n` data agrees with the level-`p+q` data. -/
lemma Wdata_le_self : ∀ (n : ℕ) (p q : ℕ), p + q ≤ n →
    (Wdata n).1 p q = (Wdata (p + q)).1 p q := by
  intro n
  induction n with
  | zero =>
      intro p q h
      obtain rfl : p = 0 := by omega
      obtain rfl : q = 0 := by omega
      rfl
  | succ n ih =>
      intro p q h
      by_cases h' : p + q ≤ n
      · have hstep : (Wdata (n + 1)).1 p q = (Wdata n).1 p q := by
          show (if h : p + q ≤ n then (Wdata n).1 p q
            else if h2 : p + q ≤ n + 1 then
              Wfill (Wdata n).1 n (Wdata n).2 p q (by omega) h2 else 0) = (Wdata n).1 p q
          rw [dif_pos h']
        rw [hstep]
        exact ih p q h'
      · have h2 : p + q = n + 1 := by omega
        exact (congrArg (fun m => (Wdata m).1 p q) h2).symm

/-- The level data is monotone: the values at a fixed bidegree do not depend on the level at which
they are read off. -/
lemma Wdata_agree (n m p q : ℕ) (hn : p + q ≤ n) (hm : p + q ≤ m) :
    (Wdata n).1 p q = (Wdata m).1 p q := by
  rw [Wdata_le_self n p q hn, Wdata_le_self m p q hm]

/-- **The acyclic-models chain**: the assembled family of model chains of the recursion. -/
noncomputable def Wz (p q : ℕ) : ↥((tMod p q).X (p + q + 1)) := (Wdata (p + q)).1 p q

theorem Wz_spec (p q : ℕ) :
    (tMod p q).d (p + q + 1) (p + q) (Wz p q) = dfc Wz p q := by
  have h1 : (tMod p q).d (p + q + 1) (p + q) (Wz p q) = dfc (Wdata (p + q)).1 p q := by
    rw [show Wz p q = (Wdata (p + q)).1 p q from rfl]
    exact (Wdata (p + q)).2 p q le_rfl
  rw [h1]
  exact dfc_congr_lt (Wdata (p + q)).1 Wz (p + q)
    (fun a b hab => Wdata_agree (p + q) (a + b) a b (by omega) le_rfl) p q le_rfl

/-- **The existence of the model chains of the acyclic-models recursion.** -/
theorem ezaw_W_exists :
    ∃ W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)),
      ∀ p q, (tMod p q).d (p + q + 1) (p + q) (W p q) = dfc W p q :=
  ⟨Wz, Wz_spec⟩

end

end Work.Kunneth
