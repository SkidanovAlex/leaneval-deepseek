import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.EntryDefs
import Submission.Work.PTCert.entryKernelSum
import Submission.Work.PTCert.fourierEntryRow
import Submission.Work.PTCert.tabOf_kleinPerm
import Submission.Work.PTCert.bval_zOfSc
import Submission.Work.PTCert.chiS_pullS
import Submission.Work.PTCert.reindexLocal

/-! Guidance from the project lead (the requester): (kept from the original file)

Context: `Submission/Work/PTCert/Glue2.lean` ... `Glue3.lean` ... and `NOTES_LEAD_glue.md`.
The auxiliary definitions used below are in `Submission/Work/PTCert/EntryDefs.lean`; the delegated
pieces are `Work.PTCert.entryKernelSum`, `Work.PTCert.fourierEntryRow`, `Work.PTCert.reindexLocal.reindexSum`
(reindexing; reproduced from `Submission.Work.PTCert.reindex.Prep`, whose module cannot be imported here
because it imports this one), `Work.PTCert.tabOf_kleinPerm` and `Work.PTCert.bval_zOfSc`.

# `EntryFormula` (glue step (G))

`kEntry rowTs k ψ i j` is the kernel's `(i,j)` entry of the `ψ`-th `Klein` block of the base
character `S = Sk k`.  Unfolding (`blockRows4`, `blockRow`, `mVal`, `xInfo`) it is
`Σ_{a<4} (-1)^{popcount (a &&& ψ)} · sign(f_a) · mVal (f_a / 2)` where `f_a` is the `a`-th field of
`ys[j]` (`sign = +1` iff `f_a` is even).  The mathematical block entry is
`psiBlock pv k ψ i j = Σ_{b : (Z/2)^2} χ_ψ(b) · χ_S(ν(y_b)) · fourierW actN (Pmat pv) S (x̄_i) (repE y_b)`,
`y_b = κ_b · x̄_j`.  The two match because (per column `b`):

* `f_a = 2 · t_a + [χ_S(μ_a) = -1]` where `κ_a · x̄_j = ν_{μ_a} rep_{t_a}` (`KleinSem`), so the low
  bit of `f_a` is `χ_S(ν(y_a))` and `f_a / 2` is the representative number `t_a` (`NStructure`);
* the Fourier block against `rep_{t_a}` is, by invariance of `Pmat` (`RowFacts`) and the row formula,
  a sum over the codes `sc < 32`, which reindexes (via `π⁻¹ ν_sc π = ν_{sc∘q}`, `χ_{pullS}`) to
  `χ_{Sp}(μ') · Row_{Sp}(r, t'')` with `π = codeElt (efPc k i) = permAut q`, `π⁻¹ · rep_{t_a} = ν_{μ'} rep_{t''}`
  — exactly what `mVal` computes, and `RowTabHyp` turns `rowVal` into the row sum.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators
open Submission.FreeGroupAut Submission.RouteB

noncomputable section

/-- The bound `efT k i < 611` for the Klein representative numbers, by evaluation of the data. -/
theorem efz_ksBound : ∀ k ≤ 5, ∀ i, efT k i < 611 := by
  intro k hk i
  have hall : (efKs k).all (fun t => decide (t < 611)) = true := by
    unfold efKs; interval_cases k <;> decide
  by_cases hi : i < (efKs k).length
  · rw [show efT k i = (efKs k)[i] from List.getD_eq_getElem _ _ hi]
    exact of_decide_eq_true (List.all_eq_true.mp hall _ (List.getElem_mem hi))
  · have hle : (efKs k).length ≤ i := by omega
    rw [show efT k i = 0 from List.getD_eq_default _ _ hle]
    norm_num

/-- Conjugation of a sign flip by a coordinate permutation: `π⁻¹ ν_s π = ν_{s ∘ q}` for
`π = permAut q` (which sends `a_k ↦ a_{q k}`). -/
theorem efz_conj_permAut_signAut (q : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) :
    (permAut q)⁻¹ * signAut s * permAut q = signAut (fun i => s (q i)) := by
  have hq : permAut q = sigAut q (fun _ => false) := by
    rw [sigAut, SigmaFacts.signAut_one, one_mul]
  have hs : signAut s = sigAut 1 s := by
    rw [sigAut, Submission.RouteB.permAut_one, mul_one]
  have hsq : signAut (fun i => s (q i)) = sigAut 1 (fun i => s (q i)) := by
    rw [sigAut, Submission.RouteB.permAut_one, mul_one]
  rw [hq, hs, hsq, SigmaFacts.sigAut_inv]
  rw [show (fun x => (fun _ : Fin 5 => false) (q x)) = (fun _ : Fin 5 => false) from rfl]
  rw [SigmaFacts.sigAut_mul]
  rw [show q.symm * 1 = q.symm from mul_one q.symm]
  rw [show (fun k => (fun _ : Fin 5 => false) k ^^ s ((q.symm).symm k))
        = (fun k => s (q k)) from by funext k; simp [Equiv.symm_symm]]
  rw [SigmaFacts.sigAut_mul]
  rw [show q.symm * q = 1 from by ext i; simp]
  rw [show (fun k => s (q k) ^^ (fun _ : Fin 5 => false) ((q.symm).symm k))
        = (fun k => s (q k)) from by funext k; simp]

/-- `(kE k i).1 = rp (efT k i)`: the code of a Klein representative is its representative code. -/
theorem efz_kE_code (hNst : NStructure) (k i : ℕ) (ht : efT k i < 611) :
    (kE k i).1 = rp (efT k i) :=
  (hNst.2.2.2.2.2 (efT k i) ht pt0).2

/-- The row element `x0E r pt0` has code `x0c r`. -/
theorem efz_x0E_code (hR : RowSem) (r : ℕ) (hr : r < 18) : (x0E r pt0).1 = x0c r := by
  have hmem : x0c r ∈ eS := by
    unfold eS; rw [List.mem_toFinset]; exact hR.2.1 r hr
  simp only [x0E, toEI, hmem, dite_true]

/-- The row formula: `Pmat pv` on a row `x0_r` is the value table. -/
theorem efz_rowFormula (hRF : RowFacts) (hR : RowSem) (pv : ℕ → ℤ) (r : ℕ) (hr : r < 18)
    (y : EI) : Pmat pv (x0E r pt0) y = (pv (keyOf r (labE r y.1)) : ℝ) :=
  (hRF pv).1 r hr (x0E r pt0) y (efz_x0E_code hR r hr)

/-- The row of a representative: `efRow k i < 18` and `efIdx k i < 120` for a representative
number `< 611`. -/
theorem efz_row_bounds (hR : RowSem) (k i : ℕ) (ht : efT k i < 611) :
    efRow k i < 18 ∧ efIdx k i < 120 :=
  ⟨(hR.2.2.1 (efT k i) ht).1, (hR.2.2.1 (efT k i) ht).2.1⟩

/-- `actE π (x0_r) = kE k i` for `π = codeElt (efPc k i)` (the tables come from `TabSem`). -/
theorem efz_kE_eq_actE (hA : ActSetup) (hNst : NStructure) (hR : RowSem) (hT : TabSem)
    (k i : ℕ) (hi : i < (efKs k).length) (ht : efT k i < 611) :
    actE (codeElt (efPc k i)) (x0E (efRow k i) pt0) = kE k i := by
  apply Subtype.ext
  obtain ⟨hr, hidx⟩ := efz_row_bounds hR k i ht
  have hPC : validPC 5 (piCodes.getD (efIdx k i) 0 / 32) = true := (hT.2 _ hidx).1
  have hTab : TabOf (codeElt (efPc k i)) (piT.get (efIdx k i)) := (hT.2 _ hidx).2.2.1
  have hlk : ∀ j < 81, lk (piT.get (efIdx k i)) j < 81 := fun j hj => ((hT.2 _ hidx).2.2.2.2 j hj).1
  rw [hA.2.2.2.2.2.2.1 _ _ hTab hlk (x0E (efRow k i) pt0)]
  rw [efz_x0E_code hR (efRow k i) hr]
  rw [efz_kE_code hNst k i ht]
  exact (hR.2.2.1 (efT k i) ht).2.2


/-- A `bif` on a `Bool` with values `1`, `-1` is a sign. -/
theorem efz_cond_eq (b : Bool) : (bif b then (1 : ℤ) else -1) = 1 ∨ (bif b then (1 : ℤ) else -1) = -1 := by
  cases b <;> simp

/-- `chiS5` is a sign. -/
theorem efz_chiS5_eq (S nu : ℕ) : chiS5 S nu = 1 ∨ chiS5 S nu = -1 := by
  rw [chiS5]
  exact efz_cond_eq _

/-- `toEI z x` is the element of code `z` when `z ∈ eS`. -/
theorem efz_toEI_of_mem {z : ℕ} (hz : z ∈ eS) (x : EI) : toEI z x = ⟨z, hz⟩ := dif_pos hz

/-- The code of the column element `κ_a · x̄_j` of the Klein block: `klT.get a` is a table of
`permAut (kleinPerm k a)` and `(kE k j).1 = rp (efT k j)`. -/
theorem efz_kapE_code (hA : ActSetup) (hNst : NStructure) (k a j : ℕ)
    (hTabK : TabOf (permAut (kleinPerm k a)) (efKl k a) ∧ (∀ j < 81, lk (efKl k a) j < 81))
    (hbval : bval (zOfSc (m := 2) a) = a) (htj : efT k j < 611) :
    (kapE k (zOfSc (m := 2) a) (kE k j)).1 = actC cmT (efKl k a) (rp (efT k j)) := by
  have h1 : kapE k (zOfSc (m := 2) a) (kE k j) = actE (permAut (kleinPerm k a)) (kE k j) := by
    simp only [kapE, hbval]
  rw [h1, hA.2.2.2.2.2.2.1 _ _ hTabK.1 hTabK.2, efz_kE_code hNst k j htj]

/-- The Klein column element knows its representative and its sign: with
`V = em (actC cmT (efKl k a) (rp (efT k j))) - 1`, `repE (κ_a · x̄_j) = repEI (V/32) pt0`,
`nuE (κ_a · x̄_j) = zOfSc (V % 32)` and `χ_{SkF k} (nuE (κ_a · x̄_j)) = chiS5 (Sk k) (V % 32)`. -/
theorem efz_columnRE (hNst : NStructure) (hBB : BitsBridge) (k a j : ℕ) (hk : k ≤ 5)
    (hcode : (kapE k (zOfSc (m := 2) a) (kE k j)).1 = actC cmT (efKl k a) (rp (efT k j))) :
    repE (kapE k (zOfSc (m := 2) a) (kE k j))
        = repEI ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32) pt0 ∧
      nuE (kapE k (zOfSc (m := 2) a) (kE k j))
        = zOfSc (m := 5) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) ∧
      chiS (SkF k) (nuE (kapE k (zOfSc (m := 2) a) (kE k j)))
        = (chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) : ℝ) := by
  have hy : em (kapE k (zOfSc (m := 2) a) (kE k j)).1 - 1
      = em (actC cmT (efKl k a) (rp (efT k j))) - 1 := by rw [hcode]
  have hlt : (em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32 < 611 := by
    have h := (hNst.2.2.2.2.1 (kapE k (zOfSc (m := 2) a) (kE k j))).1
    rwa [hy] at h
  have hmem : rp ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32) ∈ eS :=
    hNst.2.2.2.1 _ hlt
  have hSk : Sk k < 32 := by
    have h2 : 2 ^ k ≤ 32 := Nat.pow_le_pow_right (by norm_num) hk
    simp only [Sk]; omega
  have hnu : nuE (kapE k (zOfSc (m := 2) a) (kE k j))
      = zOfSc (m := 5) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) := by
    unfold nuE; rw [hy]
  refine ⟨?_, hnu, ?_⟩
  · apply Subtype.ext
    show (toEI (rp ((em (kapE k (zOfSc (m := 2) a) (kE k j)).1 - 1) / 32))
          (kapE k (zOfSc (m := 2) a) (kE k j))).1
        = (toEI (rp ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32)) pt0).1
    rw [hy, efz_toEI_of_mem hmem, efz_toEI_of_mem hmem]
  · rw [hnu, show SkF k = maskSet (m := 5) (Sk k) from rfl]
    exact hBB.2.2.1 (Sk k) _ hSk (by omega)

/-- The `a`-th field of the Klein column data of `j` is `2 t_a + [χ_S(μ_a) = -1]` with
`κ_a · x̄_j = ν_{μ_a} rep_{t_a}` (`KleinSem`). -/
theorem efz_ysField (k a j : ℕ) (hK : KleinSem k) (ha : a < 4) (hj : j < (efKs k).length) :
    efField k j a = 2 * ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32) +
        (if chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) = -1 then 1 else 0) := by
  unfold KleinSem at hK
  simp only at hK
  exact hK.2.2.2.2 j hj a ha

/-- Consequences of `efz_ysField`: `f_a / 2` is the representative number, the parity of `f_a` is the
sign `χ_S(μ_a)`, and `(if f_a % 2 = 0 then 1 else -1) = chiS5 (Sk k) (V % 32)`. -/
theorem efz_fieldArith (k a j : ℕ) (hK : KleinSem k) (ha : a < 4) (hj : j < (efKs k).length) :
    efField k j a / 2 = (em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32 ∧
      ((efField k j a % 2 = 0) ↔
        chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) = 1) ∧
      ((if efField k j a % 2 = 0 then (1 : ℝ) else -1)
        = (chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) : ℝ)) := by
  have hf := efz_ysField k a j hK ha hj
  have hchi1 := efz_chiS5_eq (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32)
  have hhalf : efField k j a / 2 = (em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32 := by
    rw [hf]
    by_cases hc : chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) = -1
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  have hpar : (efField k j a % 2 = 0) ↔
      chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) = 1 := by
    rw [hf]
    by_cases hc : chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) = -1
    · rw [if_pos hc]
      constructor
      · intro h; omega
      · intro h; omega
    · rw [if_neg hc]
      have : chiS5 (Sk k) ((em (actC cmT (efKl k a) (rp (efT k j))) - 1) % 32) = 1 := by
        rcases hchi1 with h | h
        · exact h
        · exact absurd h hc
      rw [this]
      constructor <;> intro _ <;> omega
  refine ⟨hhalf, hpar, ?_⟩
  rcases hchi1 with h1 | h1
  · rw [hpar.mpr h1, if_pos rfl, h1]; norm_num
  · have hne : ¬ (efField k j a % 2 = 0) := by rw [hpar]; omega
    rw [if_neg hne, h1]; norm_num

/-- `efzW k i Ta` is the em-value of the code of `π⁻¹ · rep_Ta` (`π` the permutation of `kE k i`). -/
def efzW (k i Ta : ℕ) : ℕ := em (actC cmT (efTabInv k i) (rp Ta)) - 1

/-- `mVal` reads the representative code `Ta` through the inverse permutation table and returns
`chiS5 (efSp k i) (W % 32) · rowVal rowTs (efRow k i) (efSp k i) (W / 32)` with `W = efzW k i Ta`. -/
theorem efz_mVal_cast (rowTs : List NT) (k i Ta : ℕ) :
    (mVal cmT eM repT rowTs (efRow k i) (efTabInv k i) (efSp k i) Ta : ℝ)
      = (chiS5 (efSp k i) (efzW k i Ta % 32) : ℝ) *
        (rowVal rowTs (efRow k i) (efSp k i) (efzW k i Ta / 32) : ℝ) := by
  rw [show mVal cmT eM repT rowTs (efRow k i) (efTabInv k i) (efSp k i) Ta
      = chiS5 (efSp k i) (efzW k i Ta % 32) *
        rowVal rowTs (efRow k i) (efSp k i) (efzW k i Ta / 32) from rfl]
  rw [Int.cast_mul]

/-- **One column of the `ψ`-block.**  For the Klein generator `a < 4` and the Klein column `j`, the
contribution `χ_S(ν(y)) · fourierW (x̄_i) (repE y)` of `y = κ_a · x̄_j` to the block entry equals the
kernel's `sign · mVal` term: the field `f_a = efField k j a` of the column data is `2 t_a + [χ_S(μ_a) = -1]`
with `κ_a · x̄_j = ν_{μ_a} rep_{t_a}`, `sign = χ_S(μ_a)` is its parity, `t_a = f_a / 2 = Ta` is the
representative number of `y`, and the Fourier block against `rep_Ta` reindexes (hypotheses `hF8`, `hF9`,
which are the statements of `fourierEntryRow` and `reindexEntryRow`) into `χ_{Sp}(μ') · Row_{Sp}(r,t'')`,
which is what `mVal` returns (`efz_mVal_cast`). -/
theorem efz_columnTerm (hA : ActSetup) (hNst : NStructure) (hBB : BitsBridge) (k a i j Ta : ℕ)
    (hK : KleinSem k) (ha : a < 4) (hj : j < (efKs k).length) (hk : k ≤ 5)
    (hTabK : TabOf (permAut (kleinPerm k a)) (efKl k a) ∧ (∀ j < 81, lk (efKl k a) j < 81))
    (hbval : bval (zOfSc (m := 2) a) = a)
    (hTa : Ta = (em (actC cmT (efKl k a) (rp (efT k j))) - 1) / 32)
    (pv : ℕ → ℤ) (rowTs : List NT)
    (hF8 : fourierW actN (Pmat pv) (SkF k) (kE k i) (repEI Ta pt0) =
      ∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))))
    (hF9 : (∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta)))) =
      (chiS5 (efSp k i) (efzW k i Ta % 32) : ℝ) *
        (rowVal rowTs (efRow k i) (efSp k i) (efzW k i Ta / 32) : ℝ)) :
    chiS (SkF k) (nuE (kapE k (zOfSc (m := 2) a) (kE k j))) *
      fourierW actN (Pmat pv) (SkF k) (kE k i) (repE (kapE k (zOfSc (m := 2) a) (kE k j)))
    = (if efField k j a % 2 = 0 then (1 : ℝ) else -1) *
      (mVal cmT eM repT rowTs (efRow k i) (efTabInv k i) (efSp k i) (efField k j a / 2) : ℝ) := by
  have htj : efT k j < 611 := efz_ksBound k hk j
  have hcode := efz_kapE_code hA hNst k a j hTabK hbval htj
  obtain ⟨hrepE, hnuE, hchiS⟩ := efz_columnRE hNst hBB k a j hk hcode
  obtain ⟨hhalf, hpar, hsign⟩ := efz_fieldArith k a j hK ha hj
  have hrepE' : repE (kapE k (zOfSc (m := 2) a) (kE k j)) = repEI Ta pt0 := by
    rw [hrepE, ← hTa]
  have hhalf' : efField k j a / 2 = Ta := by rw [hhalf, ← hTa]
  rw [hrepE', hF8, hF9, hchiS, hsign, hhalf', efz_mVal_cast]

/-- **Assembly of `EntryFormula`** from the two steps `hKS` (`kEntry` as an explicit four-term sum, i.e.
`entryKernelSum`) and the two halves `hF8`/`hF9` of the Fourier computation of one column
(`fourierEntryRow`, `reindexEntryRow`), plus the table and index facts (`tabOf_kleinPerm`, `bval_zOfSc`). -/
theorem efz_entryFormula_of (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts)
    (hK : ∀ k ≤ 5, KleinSem k) (hE : ESem) (hN : NSem) (hT : TabSem) (hR : RowSem) (hBB : BitsBridge)
    (hKS : ∀ (rowTs : List NT) (k ψ i j : ℕ), ψ < 4 → i ≤ j → j < (efKs k).length →
      (efYs k).length = (efKs k).length →
      ((kEntry rowTs k ψ i j : ℤ) : ℝ) =
        ∑ a ∈ Finset.range 4,
          (if ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) = 1 then (-1 : ℝ) else 1) *
            ((if (efField k j a) % 2 = 0 then (1 : ℝ) else -1) *
              (mVal cmT eM repT rowTs (efRow k i) (efTabInv k i) (efSp k i) (efField k j a / 2) : ℝ)))
    (hF8 : ∀ (pv : ℕ → ℤ) (k i Ta : ℕ), k ≤ 5 → i < (efKs k).length → efT k i < 611 → Ta < 611 →
      fourierW actN (Pmat pv) (SkF k) (kE k i) (repEI Ta pt0) =
        ∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
          efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))))
    (hF9 : ∀ (pv : ℕ → ℤ) (rowTs : List NT), RowTabHyp pv rowTs → ∀ (k i Ta : ℕ), k ≤ 5 →
      i < (efKs k).length → efT k i < 611 → Ta < 611 →
      (∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta)))) =
      (chiS5 (efSp k i) (efzW k i Ta % 32) : ℝ) *
        (rowVal rowTs (efRow k i) (efSp k i) (efzW k i Ta / 32) : ℝ))
    (hTabK : ∀ (k a : ℕ), k ≤ 5 → a < 4 →
      TabOf (permAut (kleinPerm k a)) (efKl k a) ∧ (∀ j < 81, lk (efKl k a) j < 81))
    (hbval : ∀ a, a < 4 → bval (zOfSc (m := 2) a) = a) :
    EntryFormula := by
  intro pv rowTs hRowTab k hk ψ hψ i j hij
  have hk5 : k ≤ 5 := by omega
  have hys : (efYs k).length = (efKs k).length := by
    have h := hK k hk5
    unfold KleinSem at h
    simp only at h
    exact h.2.2.2.1
  have hi : i.1 < (efKs k).length := i.2
  have hj : j.1 < (efKs k).length := j.2
  have hij' : i.1 ≤ j.1 := hij
  have hPb : psiBlock pv k ψ i j =
      ∑ a ∈ Finset.range 4, chiS (maskSet (m := 2) ψ) (zOfSc (m := 2) a) *
        ((if efField k j.1 a % 2 = 0 then (1 : ℝ) else -1) *
          (mVal cmT eM repT rowTs (efRow k i.1) (efTabInv k i.1) (efSp k i.1)
            (efField k j.1 a / 2) : ℝ)) := by
    show (∑ b : Fin 2 → ZMod 2, chiS (maskSet (m := 2) ψ) b *
        chiS (SkF k) (nuE (kapE k b (kE k j))) *
        fourierW actN (Pmat pv) (SkF k) (kE k i) (repE (kapE k b (kE k j)))) = _
    rw [hBB.1 2]
    rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha4 : a < 4 := Finset.mem_range.mp ha
    have htj : efT k j.1 < 611 := efz_ksBound k hk5 j.1
    have hTa611 : (em (actC cmT (efKl k a) (rp (efT k j.1))) - 1) / 32 < 611 := by
      have h := (hNst.2.2.2.2.1 (kapE k (zOfSc (m := 2) a) (kE k j.1))).1
      rw [efz_kapE_code hA hNst k a j.1 (hTabK k a hk5 ha4) (hbval a ha4) htj] at h
      exact h
    have hcol := efz_columnTerm hA hNst hBB k a i.1 j.1
      ((em (actC cmT (efKl k a) (rp (efT k j.1))) - 1) / 32) (hK k hk5) ha4 hj hk5
      (hTabK k a hk5 ha4) (hbval a ha4) rfl pv rowTs
      (hF8 pv k i.1 _ hk5 hi (efz_ksBound k hk5 i.1) hTa611)
      (hF9 pv rowTs hRowTab k i.1 _ hk5 hi (efz_ksBound k hk5 i.1) hTa611)
    rw [mul_assoc, hcol]
  have hKe := hKS rowTs k ψ i.1 j.1 hψ hij' hj hys
  rw [hPb, hKe]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [hBB.2.2.2.1 ψ a hψ (Finset.mem_range.mp ha)]

/-- **The entry formula**: the kernel block entries are the entries of the `ψ`-blocks of the
N-level Fourier matrix.  Assembled from `entryKernelSum` (the unfolding of `kEntry`), the two halves
of the Fourier computation of one column (`fourierEntryRow`, and the reindexing `reindexLocal.reindexSum`,
which is the cycle-free copy of `Submission.Work.PTCert.reindex.Prep`'s assembly), and the table/index
facts (`tabOf_kleinPerm`, `bval_zOfSc`). -/
theorem entryFormula (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts)
    (hK : ∀ k ≤ 5, KleinSem k) (hE : ESem) (hN : NSem) (hT : TabSem) (hR : RowSem) (hBB : BitsBridge) :
    EntryFormula :=
  efz_entryFormula_of hCF hA hNst hRF hK hE hN hT hR hBB
    entryKernelSum
    (fun pv k i Ta hk hi ht hTa => fourierEntryRow hCF hA hNst hRF hR hT hBB pv k i Ta hk hi ht hTa)
    (fun pv rowTs hRT k i Ta hk hi ht hTa => by
      simpa only [efzW, reindexLocal.efZ, reindexLocal.efMu, reindexLocal.efTt] using
        (reindexLocal.reindexSum hA hNst hCF hN hT hR hBB pv rowTs hRT k i Ta hk hi ht hTa))
    (fun k a hk ha => tabOf_kleinPerm hCF (hK k hk) a ha)
    (fun a ha => bval_zOfSc a ha)

end

end Work.PTCert





