import Mathlib
import Submission.Work.ATOM.ZS.Data

namespace Work.ATOM.ZS

open CategoryTheory LightProfinite

/-- If `e_k x` is already of level `< k` (i.e. `e_k x ∈ A_m` with `m < k`), then `e_{k-1} x = e_k x`.
Equivalently: for `m < k`, `e_k` and `e_{k-1}` agree on the preimage of `A_m`.  This is the
compatibility of the idempotents `e_n` of `NOTES_LEAD_solid_gaps1.md` §3.1 that makes the identity
`h₁` of REFS/03 §1 (`F ∘ T = g ∘ G`) hold also at the points where `ψ` takes the value `∞`.
Route: `e_k x = e_m x` (from `e_comp`), and `e_{k-1}` fixes `e_k x` since
`e_k x ∈ A_m ⊆ A_{k-1}` (`Work.ATOM.LevelData.A_mono`, `Work.ATOM.LevelData.e_fix_A`). -/
theorem e_pred_eq_of_mem_A (S : LightProfinite.{0}) [Infinite S] {k m : ℕ} {x : ↥S}
    (hx : Work.ATOM.e S k x ∈ Work.ATOM.A S m) (hm : m < k) :
    Work.ATOM.e S (k - 1) x = Work.ATOM.e S k x := by
  -- `A S m = range (e S m)`, so `e S k x = e S m z` for some `z`.
  obtain ⟨z, hz⟩ := hx
  have hmle : m ≤ k - 1 := by omega
  -- `e_k` followed by `e_{k-1}` is `e_{k-1}` (`e_comp`), i.e. `e_{k-1}` does not see `e_k`.
  have step1 : Work.ATOM.e S (k - 1) (Work.ATOM.e S k x) = Work.ATOM.e S (k - 1) x := by
    have h := ConcreteCategory.congr_hom (Work.ATOM.e_comp S k (k - 1)) x
    rw [CategoryTheory.comp_apply, Nat.min_eq_right (by omega : k - 1 ≤ k)] at h
    exact h
  -- `e_k x = e_m z` lies in `A_m ⊆ A_{k-1}`, and `e_{k-1}` fixes `A_{k-1}`.
  have step2 : Work.ATOM.e S (k - 1) (Work.ATOM.e S k x) = Work.ATOM.e S k x := by
    rw [← hz]
    have h := ConcreteCategory.congr_hom (Work.ATOM.e_comp S m (k - 1)) z
    rw [CategoryTheory.comp_apply, Nat.min_eq_left hmle] at h
    exact h
  rw [← step1, step2]

end Work.ATOM.ZS
