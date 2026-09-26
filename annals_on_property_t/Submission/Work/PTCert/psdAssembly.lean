import Mathlib
import Submission.Work.PTCert.Glue3

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects and the semantic Props of the data) and
`Glue3.lean` (math steps), `KernelShared.lean`/`KernelCert.lean` (the Bool check functions), the data
modules `Data/*.lean` (namespace `Submission.PTCert.D`) and the kernel theorems `Checks/*.lean`
(namespace `Submission.PTCert.C`, each `theorem xxx : <check> = true := by decide +kernel`, ALREADY BUILT).
Design notes: `NOTES_LEAD_glue.md` at the workspace root.
HARD RULES: never `decide`/`native_decide`/`simp`/`rfl` over the big data definitions (eAll, eM, the trees,
the class lists …) — they are thousands of entries; all data facts come from the Checks theorems. The only
kernel evaluation you may add is `decide +kernel` on genuinely small facts (≤ a few hundred table lookups,
e.g. `ngL.getD 0 0 = 18`, 18 row codes, `eAll = eC0 ++ … ++ eC7` IS allowed as `by decide +kernel` only
if it runs in < 60 s — otherwise prove it by `rfl`/unfolding at the list level). Never edit Checks/, Data/,
Kernel*.lean, Glue*.lean. The soundness proofs are "unfold the Bool function, turn `&&`/`allL`/`allR`/
`Nat.beq`/`bif` into ∀/∧/=/if (lemmas: Bool.and_eq_true, Nat.beq_eq, List.all_eq_true-style lemmas you prove
for allL/allR/allIdx by induction), then instantiate". Write small reusable lemmas (e.g. `allL_iff`, `allR_iff`,
`allIdx_iff`, `eqL_iff`, `strictInc → Nodup/Sorted`) in your own helper file first.
Compose: SymHyp ⇒ Pmat symmetric (SymFacts). For k ≤ 4: LdlData + (ysL.getD k []).length = nK k (from KleinSem k,
last-but-one clause) give the LdlFacts hypotheses.
LdlFacts ⇒ PSD of the symmetrised kernel matrix; EntryFormula (i ≤ j) + KleinFacts' symmetry clause
(psiBlock i j = psiBlock j i) ⇒ psiBlock pv k ψ = that matrix (Matrix.ext; case i ≤ j / j < i) ⇒ ∀ ψ < 4 PSD ⇒ WN pv (SkF k) PSD
(KleinFacts second clause). k = 5: nK 5 = 0 (ks5 = [], small decide), psiBlock is a 0×0 matrix, PSD trivially
(Matrix.PosSemidef of Fin 0 matrices), so KleinFacts gives WN pv (SkF 5) PSD. Then NLevel.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G

/-- Any matrix indexed by an empty type is positive semidefinite. -/
lemma psd_fin_zero (M : Matrix (Fin 0) (Fin 0) ℝ) : M.PosSemidef := by
  have hM : M = 0 := by ext i j; exact isEmptyElim i
  rw [hM]
  exact Matrix.PosSemidef.zero

/-- The last-but-one clause of `KleinSem k`: the length of the Klein representative list equals
`nK k`. -/
lemma kleinSem_yslen {k : ℕ} (h : KleinSem k) : (ysL.getD k []).length = nK k := by
  unfold KleinSem at h
  dsimp only at h
  exact h.2.2.2.1

theorem psdAssembly (hNL : NLevel) (hKF : KleinFacts) (hEF : EntryFormula) (hLF : LdlFacts)
    (hSF : SymFacts) (hRF : RowFacts) (hK : ∀ k ≤ 5, KleinSem k) : PsdAssembly := by
  intro pv rowTs hSym hRowTab hLDL
  -- symmetry of `Pmat pv`
  have hsym : (Pmat pv).transpose = Pmat pv := hSF pv hSym
  -- it suffices to prove PSD of the six base-character blocks
  refine hNL pv hsym fun k hk => ?_
  -- and each block follows from the PSD of its four `ψ`-blocks
  refine (hKF pv hsym k hk).2 fun ψ hψ => ?_
  by_cases hk4 : k ≤ 4
  · -- base characters `k ≤ 4`: the LDL certificate for `kEntry`
    obtain ⟨Cs, Ws, segs, accs, h1, h2, h3, h4⟩ := hLDL k hk4
    have hYs : (ysL.getD k []).length = nK k := kleinSem_yslen (hK k hk)
    have hpsd := hLF rowTs k hk4 Cs Ws segs accs h1 h2 h3 h4 hYs ψ hψ
    -- `psiBlock pv k ψ` is the symmetrised version of the kernel block
    have hEq : psiBlock pv k ψ = Matrix.of (fun (i j : Fin (nK k)) =>
        ((if i.1 ≤ j.1 then kEntry rowTs k ψ i.1 j.1 else kEntry rowTs k ψ j.1 i.1 : ℤ) : ℝ)) := by
      ext i j
      rw [Matrix.of_apply]
      by_cases hij : i.1 ≤ j.1
      · rw [if_pos hij]
        exact hEF pv rowTs hRowTab k hk4 ψ hψ i j hij
      · rw [if_neg hij]
        have hji : j.1 ≤ i.1 := by omega
        rw [(hKF pv hsym k hk).1 ψ hψ i j]
        exact hEF pv rowTs hRowTab k hk4 ψ hψ j i hji
    rw [hEq]
    exact hpsd
  · -- the last base character `k = 5`: `nK 5 = 0`, so the block is empty
    have hk5 : k = 5 := by omega
    subst hk5
    exact psd_fin_zero _

end Work.PTCert
