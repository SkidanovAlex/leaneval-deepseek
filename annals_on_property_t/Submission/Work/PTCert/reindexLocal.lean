import Mathlib
import Submission.Work.PTCert.EntryDefs
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.codeFactsAux.pcFacts
import Submission.Work.PTCert.reindex.Defs
import Submission.Work.PTCert.twistedFourierCriterion
import Submission.Work.PTCert.chiS_pullS
import Submission.Work.PTCert.reindex.bitsFacts
import Submission.Work.PTCert.reindex.codeStep

-- This module reproduces (verbatim, from the same author agent) the assembly of
-- `Submission.Work.PTCert.reindex.Prep`, which cannot be imported from `entryFormula`
-- (that module is imported by it, so importing it back would be an import cycle).
-- The declarations live in the namespace `Work.PTCert.reindexLocal` to avoid name clashes
-- with the original module.
/-!
# Reindexing of the code sum of `fourierEntryRow` (assembly)

Everything that turns the code sum `Σ_{sc<32} χ_S(sc) · pv(r, lab(π⁻¹ ν_sc rep_Ta))` of
`fourierEntryRow` into `χ_{Sp}(μ') · rowVal rowTs r Sp t`:

* the abbreviations `efQ`, `efZ`, `efMu`, `efTt`;
* the bookkeeping lemmas that extract `efIdx k i < 120`, `validPC 5 (efPc k i / 32)`, the letter
  table `efTabInv` and the `NSem` data from the hypotheses;
* the character identity `χ_S(sc) = χ_{Sp}(μ') · χ_{Sp}(Φ sc)` (`q = permOfPC (efPc k i / 32)`,
  `Sp = pullS (efPc k i / 32) S`, `Φ sc = (permCode q sc) ⊕ μ'`) from `chiS_pullS` and
  `bitsFacts`, and the code identity `codeStep`;
* `reindexSum`, the reindexing of the sum.

The target `Work.PTCert.Work.PTCert.reindexEntryRow` is a one-line application of `reindexSum`.
-/

namespace Work.PTCert


namespace reindexLocal
open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators
open Submission.FreeGroupAut Submission.RouteB

noncomputable section

/-! ## Abbreviations -/

/-- `q = permOfPC (efPc k i / 32)`: the coordinate permutation of the representative `kE k i`
(whose code `efPc k i` is divisible by `32`, so `codeElt (efPc k i) = permAut q`). -/
noncomputable def efQ (k i : ℕ) : Equiv.Perm (Fin 5) := permOfPC (efPc k i / 32)

/-- `Z = actC cmT (efTabInv k i) (rp Ta)`: the code of `π⁻¹ · rep_Ta`. -/
def efZ (k i Ta : ℕ) : ℕ := actC cmT (efTabInv k i) (rp Ta)

/-- The sign part `μ' = (em Z - 1) % 32` of `Z`. -/
def efMu (k i Ta : ℕ) : ℕ := (em (efZ k i Ta) - 1) % 32

/-- The representative number `t = (em Z - 1) / 32` of `Z`. -/
def efTt (k i Ta : ℕ) : ℕ := (em (efZ k i Ta) - 1) / 32

/-! ## Pure code arithmetic (from `bitsFacts`) -/

lemma phiC_lt' (q : Equiv.Perm (Fin 5)) (c0 sc : ℕ) : phiC q c0 sc < 32 :=
  (Work.PTCert.reindex.bitsFacts).2.2.2.2.2.2.2.2.2.1 q c0 sc

lemma zOfSc_phiC' (q : Equiv.Perm (Fin 5)) (c0 sc : ℕ) :
    zOfSc (m := 5) (phiC q c0 sc) =
      (fun i => zOfSc (m := 5) sc (q i)) + zOfSc (m := 5) c0 :=
  (Work.PTCert.reindex.bitsFacts).2.2.2.2.2.2.2.2.2.2.1 q c0 sc

lemma sum_range_phiC' (q : Equiv.Perm (Fin 5)) (c0 : ℕ) (hc0 : c0 < 32)
    {M : Type} [AddCommMonoid M] (F : ℕ → M) :
    (∑ sc ∈ Finset.range 32, F (phiC q c0 sc)) = ∑ sc ∈ Finset.range 32, F sc :=
  (Work.PTCert.reindex.bitsFacts).2.2.2.2.2.2.2.2.2.2.2.2 q c0 hc0 F

/-! ## `pullS` and `Sk` bounds -/

private lemma foldr_range_add (g : ℕ → ℕ) (n a : ℕ) :
    (List.range n).foldr (fun i acc => acc + g i) a = a + ∑ i ∈ Finset.range n, g i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ih (a + g n)]
    ring

lemma pullS_lt' (pc S : ℕ) : pullS pc S < 32 := by
  have h : pullS pc S =
      ∑ i ∈ Finset.range 5, (bif Nat.beq ((S >>> pdig pc i) % 2) 1 then 2 ^ i else 0) := by
    unfold pullS
    rw [foldr_range_add (fun i => bif Nat.beq ((S >>> pdig pc i) % 2) 1 then 2 ^ i else 0) 5 0,
      zero_add]
  rw [h]
  calc (∑ i ∈ Finset.range 5, (bif Nat.beq ((S >>> pdig pc i) % 2) 1 then 2 ^ i else 0))
      ≤ ∑ i ∈ Finset.range 5, 2 ^ i :=
        Finset.sum_le_sum (fun i _ => by cases Nat.beq ((S >>> pdig pc i) % 2) 1 <;> simp)
    _ < 32 := by decide

lemma Sk_lt' (k : ℕ) (hk : k ≤ 5) : Sk k < 32 := by
  have h2 : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hk
  simp only [Sk]
  omega

/-! ## Bookkeeping -/

lemma efIdx_lt' (hR : RowSem) (k i : ℕ) (ht : efT k i < 611) : efIdx k i < 120 :=
  (hR.2.2.1 (efT k i) ht).2.1

lemma efRow_lt' (hR : RowSem) (k i : ℕ) (ht : efT k i < 611) : efRow k i < 18 :=
  (hR.2.2.1 (efT k i) ht).1

lemma efPc_validPC (hT : TabSem) (hR : RowSem) (k i : ℕ) (ht : efT k i < 611) :
    validPC 5 (efPc k i / 32) = true :=
  (hT.2 (efIdx k i) (efIdx_lt' hR k i ht)).1

/-- The code of `π⁻¹ · rep_Ta`, where `π = codeElt (efPc k i)`. -/
lemma efZ_spec (hA : ActSetup) (hNst : NStructure) (hT : TabSem) (hR : RowSem)
    (k i Ta : ℕ) (ht : efT k i < 611) (hTa : Ta < 611) :
    (actE (codeElt (efPc k i))⁻¹ (repEI Ta pt0)).1 = efZ k i Ta := by
  obtain ⟨_, _, _, _, _, _, hTab, _, _, _, _, _⟩ := hA
  obtain ⟨_, _, _, _, _, hrepEIE⟩ := hNst
  have hidx : efIdx k i < 120 := efIdx_lt' hR k i ht
  have hTabIT : TabOf (codeElt (efPc k i))⁻¹ (efTabInv k i) := (hT.2 (efIdx k i) hidx).2.2.2.1
  have hlk : ∀ j < 81, lk (efTabInv k i) j < 81 :=
    fun j hj => ((hT.2 (efIdx k i) hidx).2.2.2.2 j hj).2
  rw [hTab (codeElt (efPc k i))⁻¹ (efTabInv k i) hTabIT hlk (repEI Ta pt0),
    (hrepEIE Ta hTa pt0).2]
  rfl

lemma efZ_mem (hA : ActSetup) (hNst : NStructure) (hT : TabSem) (hR : RowSem)
    (k i Ta : ℕ) (ht : efT k i < 611) (hTa : Ta < 611) : efZ k i Ta ∈ eAll := by
  rw [← efZ_spec hA hNst hT hR k i Ta ht hTa]
  exact List.mem_toFinset.mp (actE (codeElt (efPc k i))⁻¹ (repEI Ta pt0)).2

lemma efTt_lt' (hA : ActSetup) (hNst : NStructure) (hT : TabSem) (hR : RowSem)
    (k i Ta : ℕ) (ht : efT k i < 611) (hTa : Ta < 611) : efTt k i Ta < 611 := by
  have hNst' := hNst
  obtain ⟨_, _, _, _, hrepEE, _⟩ := hNst'
  have h := (hrepEE (actE (codeElt (efPc k i))⁻¹ (repEI Ta pt0))).1
  rw [efZ_spec hA hNst hT hR k i Ta ht hTa] at h
  exact h

lemma efMu_lt' (k i Ta : ℕ) : efMu k i Ta < 32 := Nat.mod_lt _ (by norm_num)

/-- `NSem` for the code `Z = actC cmT (efTabInv k i) (rp Ta)`: `Z = ν_{μ'} · rep_{t}`. -/
lemma efMu_nsem (hN : NSem) (hA : ActSetup) (hNst : NStructure) (hT : TabSem) (hR : RowSem)
    (k i Ta : ℕ) (ht : efT k i < 611) (hTa : Ta < 611) :
    actC cmT (ntab (efMu k i Ta)) (rp (efTt k i Ta)) = efZ k i Ta :=
  ((hN.1 (efZ k i Ta) (efZ_mem hA hNst hT hR k i Ta ht hTa)).2).2

/-! ## The character identity -/

/-- `χ_{pullS pc S}(u ∘ permOfPC pc) = χ_S(u)`: the pullback lemma `chiS_pullS` in the form
used by the reindexing. -/
lemma chiS_pullS_perm (pc : ℕ) (hpc : validPC 5 pc = true) (S : ℕ) (hS : S < 32)
    (w : Fin 5 → ZMod 2) :
    chiS (maskSet (m := 5) (pullS pc S)) (fun i => w ((permOfPC pc) i)) =
      chiS (maskSet (m := 5) S) w := by
  have h := chiS_pullS pc hpc S hS (u := fun i => w ((permOfPC pc) i))
  rw [h]
  congr 1
  funext i
  rw [Equiv.apply_symm_apply]

/-! ## The reindexing of the sum -/

/-- **The reindexing lemma.**  The code sum of `fourierEntryRow` equals `χ_{Sp}(μ') · rowVal`,
where `Sp = pullS (efPc k i / 32) (Sk k)`, `μ' = (em Z - 1) % 32`, `t = (em Z - 1) / 32` and
`Z = actC cmT (efTabInv k i) (rp Ta)`. -/
theorem reindexSum (hA : ActSetup) (hNst : NStructure) (hCF : CodeFacts) (hN : NSem)
    (hT : TabSem) (hR : RowSem) (hBB : BitsBridge) (pv : ℕ → ℤ) (rowTs : List NT)
    (hRT : RowTabHyp pv rowTs) (k i Ta : ℕ) (hk : k ≤ 5) (hi : i < (efKs k).length)
    (ht : efT k i < 611) (hTa : Ta < 611) :
    (∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta)))) =
      (chiS5 (efSp k i) (efMu k i Ta) : ℝ) *
        ((rowVal rowTs (efRow k i) (efSp k i) (efTt k i Ta)) : ℝ) := by
  have hA' := hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hNtab⟩ := hA'
  -- basic bounds and bookkeeping
  have hr : efRow k i < 18 := efRow_lt' hR k i ht
  have hidx : efIdx k i < 120 := efIdx_lt' hR k i ht
  have hvalid : validPC 5 (efPc k i / 32) = true := (hT.2 (efIdx k i) hidx).1
  have hS32 : Sk k < 32 := Sk_lt' k hk
  have hSp32 : efSp k i < 32 := pullS_lt' _ _
  have hmu32 : efMu k i Ta < 32 := efMu_lt' k i Ta
  have hphi32 : ∀ sc < 32, phiC (efQ k i) (efMu k i Ta) sc < 32 :=
    fun sc _ => phiC_lt' (efQ k i) (efMu k i Ta) sc
  have htlt : efTt k i Ta < 611 := efTt_lt' hA hNst hT hR k i Ta ht hTa
  -- the code identity
  have hcode : ∀ sc < 32, actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta)) =
      actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta)) := by
    intro sc hsc
    exact Work.PTCert.reindex.codeStep hA hNst hCF hN hT hR hBB k i Ta
      (fun sc => phiC (efQ k i) (efMu k i Ta) sc) hi ht hTa
      (fun sc _ => phiC_lt' (efQ k i) (efMu k i Ta) sc)
      (fun sc _ => zOfSc_phiC' (efQ k i) (efMu k i Ta) sc) sc hsc
  -- the character identity
  have hcrux : ∀ sc < 32, (chiS5 (Sk k) sc : ℝ) =
      (chiS5 (efSp k i) (efMu k i Ta) : ℝ) *
        (chiS5 (efSp k i) (phiC (efQ k i) (efMu k i Ta) sc) : ℝ) := by
    intro sc hsc
    have hperm : chiS (maskSet (m := 5) (efSp k i))
          (fun j => zOfSc (m := 5) sc ((efQ k i) j)) =
        chiS (maskSet (m := 5) (Sk k)) (zOfSc (m := 5) sc) :=
      chiS_pullS_perm (efPc k i / 32) hvalid (Sk k) hS32 (zOfSc (m := 5) sc)
    rw [← hBB.2.2.1 (Sk k) sc hS32 hsc,
      ← hBB.2.2.1 (efSp k i) (efMu k i Ta) hSp32 hmu32,
      ← hBB.2.2.1 (efSp k i) (phiC (efQ k i) (efMu k i Ta) sc) hSp32 (hphi32 sc hsc),
      zOfSc_phiC' (efQ k i) (efMu k i Ta) sc, chiS_add, hperm]
    have hsq : chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta)) *
        chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta)) = 1 :=
      chiS_sq _ _
    have key : chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta)) *
          (chiS (maskSet (m := 5) (Sk k)) (zOfSc (m := 5) sc) *
            chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta))) =
        chiS (maskSet (m := 5) (Sk k)) (zOfSc (m := 5) sc) := by
      calc chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta)) *
            (chiS (maskSet (m := 5) (Sk k)) (zOfSc (m := 5) sc) *
              chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta)))
          = (chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta)) *
              chiS (maskSet (m := 5) (efSp k i)) (zOfSc (m := 5) (efMu k i Ta))) *
              chiS (maskSet (m := 5) (Sk k)) (zOfSc (m := 5) sc) := by ring
        _ = chiS (maskSet (m := 5) (Sk k)) (zOfSc (m := 5) sc) := by rw [hsq, one_mul]
    exact key.symm
  -- the three rewrites of the two sides
  have hL : (∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))))
      = ∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i)
          (actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta))) :=
    Finset.sum_congr rfl (fun sc hsc => by rw [hcode sc (Finset.mem_range.mp hsc)])
  have hRT' := hRT (efRow k i) hr (efTt k i Ta) htlt (efSp k i) hSp32
  have hR1 : ((rowVal rowTs (efRow k i) (efSp k i) (efTt k i Ta) : ℤ) : ℝ)
      = ∑ sc ∈ Finset.range 32, (chiS5 (efSp k i) sc : ℝ) *
          efPv pv (efRow k i) (actC cmT (ntab sc) (rp (efTt k i Ta))) := by
    rw [hRT', Int.cast_sum]
    exact Finset.sum_congr rfl (fun sc _ => by rw [Int.cast_mul]; rfl)
  have hR2 : (∑ sc ∈ Finset.range 32, (chiS5 (efSp k i) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (ntab sc) (rp (efTt k i Ta))))
      = ∑ sc ∈ Finset.range 32, (chiS5 (efSp k i) (phiC (efQ k i) (efMu k i Ta) sc) : ℝ) *
        efPv pv (efRow k i)
          (actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta))) := by
    rw [← sum_range_phiC' (efQ k i) (efMu k i Ta) hmu32
      (fun sc => (chiS5 (efSp k i) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (ntab sc) (rp (efTt k i Ta))))]
  have hmain : (∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i)
          (actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta))))
      = (chiS5 (efSp k i) (efMu k i Ta) : ℝ) *
        (∑ sc ∈ Finset.range 32,
          (chiS5 (efSp k i) (phiC (efQ k i) (efMu k i Ta) sc) : ℝ) *
          efPv pv (efRow k i)
            (actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta)))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun sc hsc => by
      rw [hcrux sc (Finset.mem_range.mp hsc)]; ring)
  calc (∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))))
      = ∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
          efPv pv (efRow k i)
            (actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta))) := hL
    _ = (chiS5 (efSp k i) (efMu k i Ta) : ℝ) *
          (∑ sc ∈ Finset.range 32,
            (chiS5 (efSp k i) (phiC (efQ k i) (efMu k i Ta) sc) : ℝ) *
            efPv pv (efRow k i)
              (actC cmT (ntab (phiC (efQ k i) (efMu k i Ta) sc)) (rp (efTt k i Ta)))) := hmain
    _ = (chiS5 (efSp k i) (efMu k i Ta) : ℝ) *
          ((rowVal rowTs (efRow k i) (efSp k i) (efTt k i Ta)) : ℝ) := by rw [← hR2, ← hR1]

end

end reindexLocal

end Work.PTCert
