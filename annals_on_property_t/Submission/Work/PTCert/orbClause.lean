import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.sigmaGroupFacts

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-!
# `PTCert` — the orbit clause for `labE 0`

Every element `x` of the index family `EI` (the codes of `B₂`) is an `Sg`-translate of the
row code `x0c (labE 0 x)`.  This is the orbit clause used (as `hOrb`) by `Work.PTCert.rowFacts`.

The proof unwraps the N-representation of the code: `NSem` writes every code `z` as
`ν_sc · rep_t` with `t = (em z - 1)/32`, `sc = (em z - 1) % 32`, and `RowSem` writes
`rep_t = π · x0c r` with `r = rinfo t / 128`, `π = rinfo t % 128`.  The conjugating element is
therefore the product `signAut (zBool (zOfSc sc)) * codeElt (piCodes.getD π 0)`.
-/

private lemma oc_toEI_val {z : ℕ} {x : EI} (h : z ∈ eS) : (toEI z x).1 = z := by
  unfold toEI
  rw [dif_pos h]

private lemma oc_x0E_val {r : ℕ} (h : x0c r ∈ eS) : (x0E r pt0).1 = x0c r := by
  unfold x0E
  exact oc_toEI_val h

/-- `labE 0` is the row of the N-representative of the code. -/
private lemma oc_labE0_eq (z : ℕ) : labE 0 z = rinfo ((G.em z - 1) / 32) / 128 := by
  unfold labE labOf lab0
  rfl

private lemma oc_Sg_mul {s t : G5} (hs : s ∈ Sg) (ht : t ∈ Sg) : s * t ∈ Sg :=
  (sigmaGroupFacts 5).1.2.1 s hs t ht

theorem orbClause (hCF : CodeFacts) (hA : ActSetup) (hN : NSem) (hT : TabSem) (hR : RowSem) :
    ∀ x : EI, labE 0 x.1 < 18 ∧ ∃ σ ∈ Sg, actE σ (x0E (labE 0 x.1) pt0) = x := by
  intro x
  obtain ⟨-, hRx0c, hRrep, -, hRlab18, -, -, -⟩ := hR
  obtain ⟨hN1, hN2, -⟩ := hN
  obtain ⟨-, hT2⟩ := hT
  obtain ⟨-, -, -, hAmul, -, -, hAtab, -, -, -, hAsgn, hAnact⟩ := hA
  have hxmem : x.1 ∈ eAll := List.mem_toFinset.mp x.2
  refine ⟨hRlab18 x.1 hxmem, ?_⟩
  set t : ℕ := (G.em x.1 - 1) / 32 with ht
  set sc : ℕ := (G.em x.1 - 1) % 32 with hsc
  set r : ℕ := rinfo t / 128 with hr
  set pi : ℕ := rinfo t % 128 with hpi
  have ht611 : t < 611 := by rw [ht]; exact (hN1 x.1 hxmem).2.1
  have hsc32 : sc < 32 := by rw [hsc]; exact Nat.mod_lt _ (by norm_num)
  have hzcode : actC cmT (ntab sc) (rp t) = x.1 := by
    have h := (hN1 x.1 hxmem).2.2
    rw [← ht, ← hsc] at h
    exact h
  obtain ⟨hr18, hpi120, hpiEq⟩ := hRrep t ht611
  have hpiEq' : actC cmT (piT.get pi) (x0c r) = rp t := hpiEq
  have hlab : labE 0 x.1 = r := by
    rw [oc_labE0_eq x.1, hr, ht]
  have hx0es : x0c r ∈ eS := List.mem_toFinset.mpr (hRx0c r hr18)
  have hvalidpi : validPC 5 (piCodes.getD pi 0 / 32) = true := (hT2 pi hpi120).1
  have hTabpi : TabOf (codeElt (piCodes.getD pi 0)) (piT.get pi) := (hT2 pi hpi120).2.2.1
  have hBpi : ∀ k < 81, lk (piT.get pi) k < 81 := fun k hk => ((hT2 pi hpi120).2.2.2.2 k hk).1
  have hspiS : codeElt (piCodes.getD pi 0) ∈ Sg := (hCF.1 (piCodes.getD pi 0) hvalidpi).1
  have hsscS : signAut (zBool (zOfSc sc)) ∈ Sg := hAsgn (zOfSc sc)
  have hrpes : rp t ∈ eS := List.mem_toFinset.mpr (hN2 t ht611).1
  have hyval : (actE (codeElt (piCodes.getD pi 0)) (x0E r pt0)).1 = rp t := by
    rw [hAtab (codeElt (piCodes.getD pi 0)) (piT.get pi) hTabpi hBpi (x0E r pt0)]
    rw [oc_x0E_val hx0es]
    exact hpiEq'
  have hy : actE (codeElt (piCodes.getD pi 0)) (x0E r pt0) = ⟨rp t, hrpes⟩ :=
    Subtype.ext hyval
  have hzval : (actE (signAut (zBool (zOfSc sc))) (⟨rp t, hrpes⟩ : EI)).1 = x.1 :=
    (hAnact sc hsc32 (⟨rp t, hrpes⟩ : EI)).trans hzcode
  have hz : actE (signAut (zBool (zOfSc sc))) (⟨rp t, hrpes⟩ : EI) = x :=
    Subtype.ext hzval
  refine ⟨signAut (zBool (zOfSc sc)) * codeElt (piCodes.getD pi 0), oc_Sg_mul hsscS hspiS, ?_⟩
  rw [hlab, hAmul (signAut (zBool (zOfSc sc))) hsscS (codeElt (piCodes.getD pi 0)) hspiS (x0E r pt0),
    hy, hz]

end Work.PTCert
