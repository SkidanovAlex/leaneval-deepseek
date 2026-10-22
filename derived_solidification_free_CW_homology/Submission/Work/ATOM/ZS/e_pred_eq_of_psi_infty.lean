import Mathlib
import Submission.Work.ATOM.ZS.Topo.Maps
import Submission.Work.ATOM.ZS.e_pred_eq_of_mem_A

/-!
# AREA ATOM / `ℤ[S]`: `e_{k-1}` and `e_k` agree where `ψ` takes the value `∞`

`ψ(k,x)` is `∞` exactly when `e_k x` is *not* a "new point of level `k`", i.e. when `e_k x = s₀`
or the level of `e_k x` is `< k`.  In both cases `e_{k-1} x = e_k x`: this is the pointwise input
which makes the identity `h₁` of `REFS/03 §1` hold also at the points where the null sequence `g`
is not evaluated at a generator.

Route: `e_k x ∈ A_k = range (e_k)`, so `e_k x ∈ D = ⋃ A_n`; by
`Work.ATOM.levelData_mem_levelSet_iff`, either `e_k x = s₀` (and `e_{k-1}x = e_{k-1}(e_k x) = s₀`)
or `e_k x = a_j` for some `j`; in the latter case `lv (e_k x) ≠ k` by the definition of `ψ`, and
`lv (e_k x) ≤ k`, so `lv (e_k x) < k` and `Work.ATOM.ZS.e_pred_eq_of_mem_A` applies.
-/

open CategoryTheory LightProfinite LightCondensed
open OnePoint

noncomputable section

namespace Work.ATOM.ZS

/-- If `ψ(k,x) = ∞`, then `e_{k-1} x = e_k x`. -/
theorem e_pred_eq_of_psi_infty (S : LightProfinite.{0}) [Infinite S] (k : ℕ) (x : ↥S)
    (h : Work.ATOM.psiFun S (Work.ATOM.mkNS S ((k : ℕ) : ℕ∪{∞}) x) = ∞) :
    Work.ATOM.e S (k - 1) x = Work.ATOM.e S k x := by
  classical
  -- `ψ(k,x) = ∞` means that `e_k x` is not a point of `level k` different from `s₀`
  have hnot : ¬ (Work.ATOM.e S k x ∈ Set.range (Work.ATOM.levelData S).a ∧
      (Work.ATOM.levelData S).lv (Work.ATOM.e S k x) = k) := fun hc =>
    OnePoint.coe_ne_infty _ ((Work.ATOM.psiFun_some_of k hc).symm.trans h)
  -- `e_k x` lies in `A k` and hence in `D = ⋃ n, A n`
  have hA : Work.ATOM.e S k x ∈ Work.ATOM.A S k := ⟨x, rfl⟩
  have hD : Work.ATOM.e S k x ∈ Work.ATOM.levelSet S := Set.mem_iUnion.mpr ⟨k, hA⟩
  rcases (Work.ATOM.levelData_mem_levelSet_iff (S := S) (Work.ATOM.e S k x)).mp hD with
    hin | hs0
  · -- `e_k x` is an enumerated point: its level is `< k`, and `e_{k-1}` fixes it
    have hne : (Work.ATOM.levelData S).lv (Work.ATOM.e S k x) ≠ k := fun hk => hnot ⟨hin, hk⟩
    have hle : (Work.ATOM.levelData S).lv (Work.ATOM.e S k x) ≤ k :=
      Work.ATOM.levelData_lv_le hA
    have hlt : (Work.ATOM.levelData S).lv (Work.ATOM.e S k x) < k := lt_of_le_of_ne hle hne
    have hmem : Work.ATOM.e S k x ∈
        Work.ATOM.A S ((Work.ATOM.levelData S).lv (Work.ATOM.e S k x)) :=
      (Work.ATOM.levelData S).lv_mem _ hD
    exact e_pred_eq_of_mem_A S hmem hlt
  · -- `e_k x = s₀`, which is fixed by every idempotent
    have hstep : Work.ATOM.e S (k - 1) (Work.ATOM.e S k x) = Work.ATOM.e S (k - 1) x := by
      have h2 := ConcreteCategory.congr_hom (Work.ATOM.e_comp S k (k - 1)) x
      rw [ConcreteCategory.comp_apply, Nat.min_eq_right (by omega : k - 1 ≤ k)] at h2
      exact h2
    have hfix : Work.ATOM.e S (k - 1) (Work.ATOM.levelData S).s₀ = (Work.ATOM.levelData S).s₀ :=
      (Work.ATOM.levelData S).e_fix (k - 1)
    rw [← hstep, hs0, hfix]

end Work.ATOM.ZS
