import Mathlib
import Submission.Work.PTCert.EntryDefs
import Submission.Work.PTCert.sigmaGroupFacts

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators
open Submission.FreeGroupAut Submission.RouteB

set_option maxRecDepth 10000

/-! ## Helpers for `fourierEntryRow` -/

/-- `Sk k = 2^k - 1 < 32` for `k ≤ 5`. -/
private lemma Sk_lt_32 (k : ℕ) (hk : k ≤ 5) : Sk k < 32 := by
  interval_cases k <;> norm_num [Sk]

/-- `toEI z x` has code `z` when `z` is a code. -/
private lemma toEI_val_of (z : ℕ) (x : EI) (h : z ∈ eS) : (toEI z x).1 = z := by
  unfold toEI
  rw [dif_pos h]

/-- The row code `x0c r` (`r < 18`) is a code. -/
private lemma x0c_mem_eS' (hR : RowSem) (r : ℕ) (hr : r < 18) : x0c r ∈ eS :=
  List.mem_toFinset.mpr (hR.2.1 r hr)

/-- The base point `x0E r pt0` has code `x0c r`. -/
private lemma x0E_val' (hR : RowSem) (r : ℕ) (hr : r < 18) : (x0E r pt0).1 = x0c r := by
  unfold x0E
  exact toEI_val_of (x0c r) pt0 (x0c_mem_eS' hR r hr)

/-- `Sg` contains `1`. -/
private lemma Sg_one' : (1 : G5) ∈ Sg := (sigmaGroupFacts 5).1.1

/-- `Sg` is closed under products. -/
private lemma Sg_mul' {s t : G5} (hs : s ∈ Sg) (ht : t ∈ Sg) : s * t ∈ Sg :=
  (sigmaGroupFacts 5).1.2.1 s hs t ht

/-- `Sg` is closed under inverses. -/
private lemma Sg_inv' {s : G5} (hs : s ∈ Sg) : s⁻¹ ∈ Sg := (sigmaGroupFacts 5).1.2.2 s hs

/-- The representative `kE k i` has code `rp (efT k i)`. -/
private lemma kE_val' (hNst : NStructure) (k i : ℕ) (ht : efT k i < 611) :
    (kE k i).1 = rp (efT k i) :=
  (hNst.2.2.2.2.2 (efT k i) ht pt0).2

/-- The value of the base character `Sk k` on the code character `zOfSc sc`. -/
private lemma chiS_SkF_zOfSc (hBB : BitsBridge) (k sc : ℕ) (hk : k ≤ 5) (hsc : sc < 32) :
    chiS (SkF k) (zOfSc sc) = (chiS5 (Sk k) sc : ℝ) :=
  hBB.2.2.1 (Sk k) sc (Sk_lt_32 k hk) hsc

/-- Unfolding of the untwisted Fourier block on the concrete action `actN`. -/
private lemma fourierW_actN (M : Matrix EI EI ℝ) (S : Finset (Fin 5)) (x y : EI) :
    fourierW actN M S x y = ∑ a : Fin 5 → ZMod 2, chiS S a * M x (actN a y) := rfl

/-- `π = codeElt (efPc k i)` carries the base point `x0E (efRow k i) pt0` to `kE k i`. -/
private lemma actE_efPc_x0E (hA : ActSetup) (hNst : NStructure) (hR : RowSem) (hT : TabSem)
    (k i : ℕ) (ht : efT k i < 611) :
    actE (codeElt (efPc k i)) (x0E (efRow k i) pt0) = kE k i := by
  obtain ⟨_, _, _, _, _, _, hAtab, -, -, -, -, -⟩ := hA
  obtain ⟨hr18, hidx120, hrow⟩ := hR.2.2.1 (efT k i) ht
  obtain ⟨-, -, hTabT, -, hBoth⟩ := hT.2 (efIdx k i) hidx120
  apply Subtype.ext
  rw [hAtab (codeElt (efPc k i)) (piT.get (efIdx k i)) hTabT
      (fun j hj => (hBoth j hj).1) (x0E (efRow k i) pt0),
    x0E_val' hR (efRow k i) hr18]
  exact hrow.trans (kE_val' hNst k i ht).symm

/-- **The pointwise entry identity**: the `Pmat pv`-entry of a row of the Klein representative
against `ν_sc · rep_Ta` is the value table entry at the code of `π⁻¹ ν_sc rep_Ta`. -/
private lemma pm_entry (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts)
    (hR : RowSem) (hT : TabSem) (pv : ℕ → ℤ) (k i Ta sc : ℕ)
    (ht : efT k i < 611) (hTa : Ta < 611) (hsc : sc < 32) :
    Pmat pv (kE k i) (actN (zOfSc sc) (repEI Ta pt0)) =
      efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))) := by
  classical
  have hA' := hA
  obtain ⟨-, -, -, hAcomp, hAone, -, hAtab, -, -, -, -, hNtab⟩ := hA'
  obtain ⟨hr18, hidx120, -⟩ := hR.2.2.1 (efT k i) ht
  obtain ⟨hvalPC, -, hTabT, hTabI, hBoth⟩ := hT.2 (efIdx k i) hidx120
  have hltI : ∀ j < 81, lk (efTabInv k i) j < 81 := fun j hj => (hBoth j hj).2
  have hπS : codeElt (efPc k i) ∈ Sg := (hCF.1 (efPc k i) hvalPC).1
  have hπinvS : (codeElt (efPc k i))⁻¹ ∈ Sg := Sg_inv' hπS
  have hx0 : (x0E (efRow k i) pt0).1 = x0c (efRow k i) := x0E_val' hR (efRow k i) hr18
  have hkE : actE (codeElt (efPc k i)) (x0E (efRow k i) pt0) = kE k i :=
    actE_efPc_x0E hA hNst hR hT k i ht
  have hrepTa : (repEI Ta pt0).1 = rp Ta := (hNst.2.2.2.2.2 Ta hTa pt0).2
  have hWv : actE (codeElt (efPc k i))
        (actE (codeElt (efPc k i))⁻¹ (actN (zOfSc sc) (repEI Ta pt0)))
      = actN (zOfSc sc) (repEI Ta pt0) := by
    rw [← hAcomp (codeElt (efPc k i)) hπS (codeElt (efPc k i))⁻¹ hπinvS
        (actN (zOfSc sc) (repEI Ta pt0)), mul_inv_cancel, hAone]
  have hv1 : (actE (codeElt (efPc k i))⁻¹ (actN (zOfSc sc) (repEI Ta pt0))).1
      = actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta)) := by
    rw [hAtab (codeElt (efPc k i))⁻¹ (efTabInv k i) hTabI hltI (actN (zOfSc sc) (repEI Ta pt0)),
      hNtab sc hsc (repEI Ta pt0), hrepTa]
  calc Pmat pv (kE k i) (actN (zOfSc sc) (repEI Ta pt0))
      = Pmat pv (actE (codeElt (efPc k i)) (x0E (efRow k i) pt0))
          (actE (codeElt (efPc k i))
            (actE (codeElt (efPc k i))⁻¹ (actN (zOfSc sc) (repEI Ta pt0)))) := by
        rw [← hkE]
        exact congrArg (fun z => Pmat pv (actE (codeElt (efPc k i)) (x0E (efRow k i) pt0)) z)
          hWv.symm
    _ = Pmat pv (x0E (efRow k i) pt0)
          (actE (codeElt (efPc k i))⁻¹ (actN (zOfSc sc) (repEI Ta pt0))) :=
        (hRF pv).2.1 (codeElt (efPc k i)) hπS (x0E (efRow k i) pt0)
          (actE (codeElt (efPc k i))⁻¹ (actN (zOfSc sc) (repEI Ta pt0)))
    _ = efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))) := by
        rw [(hRF pv).1 (efRow k i) hr18 (x0E (efRow k i) pt0)
              (actE (codeElt (efPc k i))⁻¹ (actN (zOfSc sc) (repEI Ta pt0))) hx0, hv1]
        simp only [efPv]


namespace Work.PTCert

/-- The Fourier block of a row of the Klein representative `kE k i = rep_{efT k i} = π · x₀_r`
(`r = efRow k i`, `π = codeElt (efPc k i)`, where `efPc k i = piCodes.getD (efIdx k i) 0`,
`efIdx k i = rinfo (efT k i) % 128`), against the representative `rep_Ta` (`Ta < 611`), in the codes of
the value table `pv`.  `RowSem` gives `actC cmT (piT.get (efIdx k i)) (x0c (efRow k i)) = rp (efT k i)`,
so with `ActSetup`'s `TabOf` clause (`hT`), `actE π (x0E (efRow k i) pt0) = kE k i`, and
`fourierW actN (Pmat pv) (SkF k) (kE k i) (repEI Ta pt0) = Σ_a χ_{SkF k}(a) · P(x̄_i, ν_a rep_Ta)`
becomes a sum over codes `sc < 32` (`BitsBridge`, `χ_S ∘ zOfSc = χ5`, `hk`), where invariance of
`Pmat pv` under the conjugation action (`RowFacts`, with `π ∈ Sg` from `CodeFacts`) and the row formula
`P(x₀_r, y) = pv (keyOf r (labE r y.1))` give
`P(x̄_i, ν_sc rep_Ta) = pv (keyOf r (labE r (π⁻¹ ν_sc rep_Ta).1))`, with
`(π⁻¹ ν_sc rep_Ta).1 = actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))` (`ActSetup`, `TabSem`),
`efTabInv k i = piIT.get (efIdx k i)` being a table of `π⁻¹`. -/
theorem fourierEntryRow (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts)
    (hR : RowSem) (hT : TabSem) (hBB : BitsBridge) (pv : ℕ → ℤ) (k i Ta : ℕ) (hk : k ≤ 5)
    (hi : i < (efKs k).length) (ht : efT k i < 611) (hTa : Ta < 611) :
    fourierW actN (Pmat pv) (SkF k) (kE k i) (repEI Ta pt0) =
      ∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))) := by
  rw [fourierW_actN]
  rw [hBB.1 5 (fun a => chiS (SkF k) a * Pmat pv (kE k i) (actN a (repEI Ta pt0)))]
  rw [show (2 : ℕ) ^ 5 = 32 from by norm_num]
  refine Finset.sum_congr rfl (fun sc hsc => ?_)
  have hsc' : sc < 32 := Finset.mem_range.mp hsc
  show chiS (SkF k) (zOfSc sc) * Pmat pv (kE k i) (actN (zOfSc sc) (repEI Ta pt0)) =
    (chiS5 (Sk k) sc : ℝ) *
      efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta)))
  rw [chiS_SkF_zOfSc hBB k sc hk hsc',
    pm_entry hCF hA hNst hRF hR hT pv k i Ta sc ht hTa hsc']


end Work.PTCert

/-- The same statement as `Work.PTCert.Work.PTCert.fourierEntryRow`, in the outer namespace
(the file's duplicate `namespace Work.PTCert` puts the requested declaration one level deeper). -/
theorem fourierEntryRow (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts)
    (hR : RowSem) (hT : TabSem) (hBB : BitsBridge) (pv : ℕ → ℤ) (k i Ta : ℕ) (hk : k ≤ 5)
    (hi : i < (efKs k).length) (ht : efT k i < 611) (hTa : Ta < 611) :
    fourierW actN (Pmat pv) (SkF k) (kE k i) (repEI Ta pt0) =
      ∑ sc ∈ Finset.range 32, (chiS5 (Sk k) sc : ℝ) *
        efPv pv (efRow k i) (actC cmT (efTabInv k i) (actC cmT (ntab sc) (rp Ta))) :=
  Work.PTCert.Work.PTCert.fourierEntryRow hCF hA hNst hRF hR hT hBB pv k i Ta hk hi ht hTa
