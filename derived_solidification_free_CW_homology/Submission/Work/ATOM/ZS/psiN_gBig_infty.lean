import Mathlib
import Submission.Work.ATOM.ZS.PsiLiftDefs
import Submission.Work.ATOM.ZS.e_pred_eq_of_psi_infty

/-!
# AREA ATOM / `ℤ[S]`: `ẽ ∘ shift = ẽ` at the points where `ψ` takes the value `∞`

The null sequence `g : P ⟶ ℤ[S]` of `REFS/03 §1` is built so that the identity `h₁`
(`(1-S) ⊗ id ≫ F = G ≫ g̃`) is checked after pulling back along the epimorphism
`ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]`.  On `(ℕ∪{∞}) × S` the left-hand side is `G`, which is supported
on `T' = {(j,a_j)} ∪ {∞} × S`; the right-hand side is `g̃ ∘ ψ_P`, and `ψ_P(p) = ∞` is the value
of `ψ` *off* `T'`.  Hence the identity only closes if `ẽ` is constant along the shift at those
points, which is the statement proved here:

* `p = (∞,x)`: both sides are `x`;
* `p = (k,x)` with `k ≥ 1` and `ψ(k,x) = ∞`: `ẽ(k,x) = e_k x` and `ẽ((k,x)) = e_{k-1} x`, and
  `Work.ATOM.ZS.e_pred_eq_of_psi_infty` gives `e_{k-1} x = e_k x`;
* `p = (0,x)`: `ẽ(0,x) = e_0 x = e_{0-1} x`, and the value is `s₀` precisely because
  `ψ(0,x) = ∞` says that `e_0 x` (which lies in `A_0`, hence in `D` and is of level `≤ 0`) is not
  an enumerated point; by `Work.ATOM.levelData_mem_levelSet_iff` it is therefore `s₀`
  (helper `e_zero_of_psi_infty`).
-/

open CategoryTheory Limits LightProfinite LightCondensed
open OnePoint
open scoped LightProfinite

noncomputable section

namespace Work.ATOM.ZS

/-- If `ψ(0,x) = ∞`, then `e_0 x = s₀`.

Indeed, `e_0 x ∈ A 0 ⊆ D = ⋃ n, A n`, so `e_0 x = s₀` or `e_0 x = a_j` for some `j`
(`Work.ATOM.levelData_mem_levelSet_iff`); in the second case `lv (e_0 x) ≤ 0`, hence
`lv (e_0 x) = 0`, so `Work.ATOM.psiFun_some_of` computes `ψ(0,x) = idx (e_0 x) ≠ ∞`,
contradicting the hypothesis. -/
theorem e_zero_of_psi_infty (S : LightProfinite.{0}) [Infinite S] (x : ↥S)
    (h : Work.ATOM.psiFun S (Work.ATOM.mkNS S (((0 : ℕ) : ℕ∪{∞})) x) = OnePoint.infty) :
    Work.ATOM.e S 0 x = (Work.ATOM.levelData S).s₀ := by
  classical
  have hA : Work.ATOM.e S 0 x ∈ Work.ATOM.A S 0 := ⟨x, rfl⟩
  have hD : Work.ATOM.e S 0 x ∈ Work.ATOM.levelSet S := Set.mem_iUnion.mpr ⟨0, hA⟩
  have hnot : ¬ (Work.ATOM.e S 0 x ∈ Set.range (Work.ATOM.levelData S).a) := by
    rintro ⟨j, hj⟩
    have hlev : (Work.ATOM.levelData S).lv (Work.ATOM.e S 0 x) = 0 :=
      le_antisymm (Work.ATOM.levelData_lv_le hA) (Nat.zero_le _)
    have hc : Work.ATOM.e S 0 x ∈ Set.range (Work.ATOM.levelData S).a ∧
        (Work.ATOM.levelData S).lv (Work.ATOM.e S 0 x) = 0 := ⟨⟨j, hj⟩, hlev⟩
    have h2 : (((Work.ATOM.levelData S).idx (Work.ATOM.e S 0 x) : ℕ) : ℕ∪{∞}) = OnePoint.infty :=
      (Work.ATOM.psiFun_some_of (S := S) 0 hc).symm.trans h
    exact OnePoint.coe_ne_infty _ h2
  rcases (Work.ATOM.levelData_mem_levelSet_iff (S := S) (Work.ATOM.e S 0 x)).mp hD with hin | hs0
  · exact absurd hin hnot
  · exact hs0

/-- **`ẽ` is constant along the shift at the points where `ψ = ∞`.**  In the notation of
`NOTES_LEAD_solid_gaps1.md` §3.1: `ẽ(k+1,x) = ẽ(k,x)` whenever `ψ(k,x) = ∞`.  This is the
pointwise input of the identity `h₁` of `REFS/03 §1`. -/
theorem psiN_gBig_infty (S : LightProfinite.{0}) [Infinite S] (p : ↥(Work.ATOM.NS S))
    (h : Work.ATOM.psiN S p = OnePoint.infty) :
    Work.ATOM.eShift S p = Work.ATOM.ePred S p := by
  classical
  -- The core of the argument, for the finite points `(k,x)` of `(ℕ∪{∞}) × S`.
  have HK : ∀ (k : ℕ) (x : ↥S),
      Work.ATOM.psiN S (Work.ATOM.mkNS S ((k : ℕ) : ℕ∪{∞}) x) = OnePoint.infty →
      Work.ATOM.eShift S (Work.ATOM.mkNS S ((k : ℕ) : ℕ∪{∞}) x) =
        Work.ATOM.ePred S (Work.ATOM.mkNS S ((k : ℕ) : ℕ∪{∞}) x) := by
    intro k x hψ
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- `k = 0`: both sides are `s₀` (`e_0 x = s₀` by `e_zero_of_psi_infty`).
      subst hk
      have h0 : Work.ATOM.e S 0 x = (Work.ATOM.levelData S).s₀ :=
        e_zero_of_psi_infty S x hψ
      exact (Work.ATOM.eShift_some (S := S) 0 x).trans
        (h0.trans (Work.ATOM.ePred_zero (S := S) x).symm)
    · -- `k ≥ 1`: write `k = k' + 1`; then `eShift(k' + 1,x) = e_{k'} x` and
      -- `ePred(k' + 1,x) = e_{k'} x = e_{k'+1} x` by `e_pred_eq_of_psi_infty`.
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hψf : Work.ATOM.psiFun S (Work.ATOM.mkNS S (((k' + 1 : ℕ) : ℕ∪{∞})) x) = OnePoint.infty :=
        hψ
      have he := Work.ATOM.ZS.e_pred_eq_of_psi_infty S (k' + 1) x hψf
      exact (Work.ATOM.eShift_some (S := S) (k' + 1) x).trans
        (he.symm.trans (Work.ATOM.ePred_succ (S := S) k' x).symm)
  obtain ⟨k, x⟩ := p
  match k with
  | Option.none =>
    -- `p = (∞,x)`: both `eShift` and `ePred` are the identity there.
    exact (Work.ATOM.eShift_infty (S := S) x).trans (Work.ATOM.ePred_infty (S := S) x).symm
  | Option.some k => exact HK k x h

end Work.ATOM.ZS
