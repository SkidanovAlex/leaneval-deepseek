import Mathlib
import Submission.Work.Peluse.UControl.levAssemblyDefs

/-!
# Evaluating the direction polynomial at the direction of the nested PET datum

`dirPoly d lc P c j v` (`levDatum.lean`) is the polynomial recursion of Peluse's §3 built in the
free ring `MvPolynomial ℕ ℤ`: `dirPoly 0 = C lc` and
`dirPoly (j+1) v = Σ_{s ∈ v} C (d - j)·dirPoly j (P j s)·X (c (j+1) s)`.  `IdxDatum.dir` is the same
recursion evaluated in `ℤ`.  This file proves the bridge between the two: evaluating `dirPoly` at a
parameter function `φ` that inverts the coordinate map `c` (`φ (c i s) = v i s`) gives exactly the
datum's direction `dir` at the corresponding index.

The only structural input is that the datum's attachment `par j k` is the raw set `P j k`, read
through the inclusion `range (N j) → Fin (N j)` (lemma `levPar_val_map`); the rest is the induction
on the level.
-/

namespace Work.Peluse.UControl

noncomputable section

set_option autoImplicit false

/-- The recursion equation of `IdxDatum.dir` at a successor level.  (A copy of
`levelCompareDefs.IdxDatum.dir_succ`, which is not in this file's import closure.) -/
private lemma idxDir_succ (D : IdxDatum) (l : ℕ) (c : ℤ) (j : ℕ) (w : D.I (j+1))
    (a : (j : ℕ) → D.S j → ℤ) :
    D.dir l c (j + 1) w a
      = ∑ s ∈ w.val, ((l : ℤ) - (j : ℤ)) * D.dir l c j (D.par j s) a * a (j + 1) s := by
  simp only [IdxDatum.dir]

/-- **The attachment of `levDatumOf` is the raw index set.**  Reading the datum's `par j k` back
along `Fin.val` recovers the raw set `P j k`. -/
private lemma levPar_val_map {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty)
    (j : ℕ) (k : Fin (N (j+1))) :
    (((levDatumOf N P hsub hne).par j k).val.map (Fin.valEmbedding (n := N j))) = P j k.1 := by
  show Finset.map (Fin.valEmbedding (n := N j))
        (Finset.map (levEmb hsub j k) (P j k.1).attach) = P j k.1
  rw [Finset.map_map]
  have h : (levEmb hsub j k).trans (Fin.valEmbedding (n := N j))
      = Function.Embedding.subtype (fun x => x ∈ P j k.1) := by
    apply Function.Embedding.ext
    intro x
    rfl
  rw [h]
  exact Finset.attach_map_val

/-- **The direction bridge.**  Evaluating the recursion polynomial `dirPoly` at `φ` gives the
datum's direction `dir`, for every level and every index. -/
private lemma dirPoly_eval_eq_dir {d : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ}
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty)
    (v : ℕ → ℕ → ℤ) (φ : ℕ → ℤ)
    (hφ : ∀ i (s : Fin (N i)), φ (c i s.1) = v i s.1) :
    ∀ (j : ℕ) (t : Finset (Fin (N j))) (ht : t.Nonempty),
      MvPolynomial.eval φ (dirPoly d lc P c j (t.map Fin.valEmbedding))
        = (levDatumOf N P hsub hne).dir d lc j ⟨t, ht⟩ (fun i s => v i s.1) := by
  intro j
  induction j with
  | zero =>
    intro t ht
    simp only [dirPoly_zero, MvPolynomial.eval_C, IdxDatum.dir]
  | succ j ih =>
    intro t ht
    have hR := idxDir_succ (levDatumOf N P hsub hne) d lc j ⟨t, ht⟩ (fun i s => v i s.1)
    rw [dirPoly_succ, MvPolynomial.eval_sum, Finset.sum_map, hR]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    simp only [Fin.valEmbedding_apply]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    have hkey : MvPolynomial.eval φ (dirPoly d lc P c j (P j s.1))
        = (levDatumOf N P hsub hne).dir d lc j ((levDatumOf N P hsub hne).par j s)
            (fun i s => v i s.1) := by
      rw [← levPar_val_map hsub hne j s]
      exact ih ((levDatumOf N P hsub hne).par j s).val ((levDatumOf N P hsub hne).par j s).2
    rw [hkey, hφ (j + 1) s]

theorem dirPolyEvalDir {d : Nat} {lc : Int} {N : Nat -> Nat} {P : Nat -> Nat -> Finset Nat}
    {c : Nat -> Nat -> Nat} {L' : Nat} {hL' : 1 ≤ L'} {X : Work.Peluse.UControl.HistData d L'}
    {f0 : Fin L' -> Bool}
    (h : Work.Peluse.UControl.LevDInv d lc (d - 1) L' hL' N P c X f0)
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty)
    (v : Nat -> Nat -> Int) (φ : Nat -> Int)
    (hφ : ∀ i (s : Fin (N i)), φ (c i s.1) = v i s.1)
    (j' : Nat) (w : (Work.Peluse.UControl.levDatumOf N P hsub hne).I j') :
    MvPolynomial.eval φ (Work.Peluse.UControl.dirPoly d lc P c j'
        (w.val.map ⟨fun s => s.1, fun a b hab => Fin.ext hab⟩))
      = (Work.Peluse.UControl.levDatumOf N P hsub hne).dir d lc j' w (fun i s => v i s.1) := by
  exact dirPoly_eval_eq_dir (d := d) (lc := lc) (N := N) (P := P) (c := c)
    hsub hne v φ hφ j' w.val w.2

end

end Work.Peluse.UControl
