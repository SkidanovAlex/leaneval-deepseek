import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# `Work.PTCert.symFacts` — symmetry of `Pmat pv` from `SymHyp pv`

The value table `pv` on the group keys `(r, g)` is *transpose consistent* (`SymHyp`).  We prove
that the matrix `Pmat pv` (the `Σ`-average of the row-supported matrix `Umat pv`) is symmetric.

Sketch (see `NOTES_LEAD_glue.md`):
* `genSym` (the heart): for a row code `x₀_r` and a group representative `z = grepE r g`,
  `P (x₀_r, z) = P (z, x₀_r)`.  `P (x₀_r, z) = pv (key r g)` by the row formula (`RowFacts`),
  while `z = ν_sc · π_i · x₀_{r'}` (`NSem` + `RowSem`), so `P (z, x₀_r) = P (x₀_{r'}, (ν π)⁻¹ x₀_r)`
  by invariance and the row formula again; `SymHyp` identifies the two values.
* `centralSym`: for every `r` and every `y`, `P (x₀_r, y) = P (y, x₀_r)`: `y` is a stabiliser
  translate of its group representative (row `≥ 1`, `GroupSem`), or a group-translate of a row
  representative (row `0`, `RowFacts` orbit clause).
* General `x, y`: `x` is a `Sg`-translate of `x₀_{labE 0 x}` (`RowFacts`), and invariance plus
  the central case give `P x y = P y x`.
-/

set_option maxRecDepth 400000
set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-- The code of the identity element is `0`. -/
private lemma actCode_zero (c : ℕ) : actCode c 0 = 0 := by
  unfold actCode
  simp only [Nat.zero_div, Nat.zero_mod, Submission.PTCert.actL]
  simp [Submission.PTCert.normC, Submission.PTCert.invLk]

/-- `actCode` and `actC` agree when the letter table computes `actL`. -/
private lemma actCode_eq_actC (c tab z : ℕ)
    (h : ∀ k < 81, lk tab k = Submission.PTCert.actL 5 (c / 32) (c % 32) k)
    (h1 : z / 128 < 81) (h2 : z % 128 < 81) : actCode c z = actC cmT tab z := by
  unfold actCode Submission.PTCert.actC
  rw [← h (z / 128) h1, ← h (z % 128) h2]

/-- Membership of `List.getD`. -/
private lemma getD_mem (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem (hn := hi)]
  exact List.getElem_mem hi

/-- **(step 1)** Symmetry at the group representatives: for `z = grepE r g` (and `x` a row code
`x₀_r`), `P (x, z) = P (z, x)`. -/
private lemma genSym (hCF : CodeFacts) (hA : ActSetup) (hRF : RowFacts) (hN : NSem)
    (hT : TabSem) (hR : RowSem) (hG : GroupSem)
    (pv : ℕ → ℤ) (hsym : SymHyp pv)
    (r : ℕ) (hr : r < 18) (g : ℕ) (hg : g < ngE r)
    (zE xE : EI) (hz : zE.1 = grepE r g) (hx : xE.1 = x0c r) :
    Pmat pv xE zE = Pmat pv zE xE := by
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  obtain ⟨-, -, -, hmul, hone, -, htab, -, -, -, -, -⟩ := hA
  have hactinv2 : ∀ σ ∈ Sg, ∀ x : EI, actE σ (actE σ⁻¹ x) = x := by
    intro σ hσ x
    rw [← hmul σ hσ σ⁻¹ (hSg.2.2 σ hσ) x, mul_inv_cancel, hone]
  have hPinv : ∀ σ ∈ Sg, ∀ a b : EI, Pmat pv (actE σ a) b = Pmat pv a (actE σ⁻¹ b) := by
    intro σ hσ a b
    have h := (hRF pv).2.1 σ hσ a (actE σ⁻¹ b)
    rwa [hactinv2 σ hσ b] at h
  have hzEeAll : zE.1 ∈ eAll := List.mem_toFinset.mp zE.2
  obtain ⟨h1em, htlt, hNz⟩ := hN.1 zE.1 hzEeAll
  obtain ⟨-, hR2, hR3, hR4, -, -, -, -⟩ := hR
  obtain ⟨hr'lt, hilt, hRep⟩ := hR3 ((em zE.1 - 1) / 32) htlt
  obtain ⟨hTsig, hTpi⟩ := hT
  have hsc32 : (em zE.1 - 1) % 32 < 32 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hTabSig, hlkSig⟩ := hTsig ((em zE.1 - 1) % 32) hsc32
  obtain ⟨hvalid, hmod0, hTabPi, hTabPiI, hlkAll⟩ := hTpi (rinfo ((em zE.1 - 1) / 32) % 128) hilt
  have hlkPi : ∀ k < 81, lk (piT.get (rinfo ((em zE.1 - 1) / 32) % 128)) k < 81 := fun k hk => (hlkAll k hk).1
  have hlkPiI : ∀ k < 81, lk (piIT.get (rinfo ((em zE.1 - 1) / 32) % 128)) k < 81 := fun k hk => (hlkAll k hk).2
  have hpiSg : codeElt (piCodes.getD (rinfo ((em zE.1 - 1) / 32) % 128) 0) ∈ Sg := (hCF.1 _ hvalid).1
  have hνSg : signAut (scBits ((em zE.1 - 1) % 32)) ∈ Sg := by
    apply (sigmaGroupFacts 5).2.2
    rw [SigmaFacts.mem_SignSet_iff]
    exact ⟨_, rfl⟩
  set π : G5 := codeElt (piCodes.getD (rinfo ((em zE.1 - 1) / 32) % 128) 0) with hπdef
  set ν : G5 := signAut (scBits ((em zE.1 - 1) % 32)) with hνdef
  have hπSg : π ∈ Sg := hpiSg
  have hνSg' : ν ∈ Sg := hνSg
  have hrptmem : rp ((em zE.1 - 1) / 32) ∈ eAll := (hN.2.1 _ htlt).1
  set rep2 : EI := ⟨rp ((em zE.1 - 1) / 32), List.mem_toFinset.mpr hrptmem⟩ with hrepdef
  set xF : EI := ⟨x0c (rinfo ((em zE.1 - 1) / 32) / 128), List.mem_toFinset.mpr (hR2 _ hr'lt)⟩ with hxFdef
  have hπx : actE π xF = rep2 := by
    apply Subtype.ext
    show (actE π xF).1 = rp ((em zE.1 - 1) / 32)
    rw [htab π (piT.get (rinfo ((em zE.1 - 1) / 32) % 128)) hTabPi hlkPi xF, hRep]
  have hνrep : actE ν rep2 = zE := by
    apply Subtype.ext
    show (actE ν rep2).1 = zE.1
    rw [htab ν (ntab ((em zE.1 - 1) % 32)) hTabSig hlkSig rep2, hNz]
  have hzEq : zE = actE (ν * π) xF := by
    rw [hmul ν hνSg' π hπSg xF, hπx, hνrep]
  have hνπSg : ν * π ∈ Sg := hSg.2.1 ν hνSg' π hπSg
  have hP1 : Pmat pv zE xE = Pmat pv xF (actE ((ν * π)⁻¹) xE) := by
    rw [hzEq]
    exact hPinv (ν * π) hνπSg xF xE
  have hνπinv : (ν * π)⁻¹ = π⁻¹ * ν := by
    rw [mul_inv_rev]
    show π⁻¹ * (signAut (scBits ((em zE.1 - 1) % 32)))⁻¹ = π⁻¹ * ν
    rw [SigmaFacts.signAut_inv]
  have hfin : (actE ((ν * π)⁻¹) xE).1 =
      actC cmT (piIT.get (rinfo ((em zE.1 - 1) / 32) % 128))
        (actC cmT (ntab ((em zE.1 - 1) % 32)) (x0c r)) := by
    rw [hνπinv]
    rw [hmul π⁻¹ (hSg.2.2 π hπSg) ν hνSg' xE]
    rw [htab π⁻¹ (piIT.get (rinfo ((em zE.1 - 1) / 32) % 128)) hTabPiI hlkPiI (actE ν xE)]
    rw [htab ν (ntab ((em zE.1 - 1) % 32)) hTabSig hlkSig xE]
    rw [hx]
  have hP2 : Pmat pv xF (actE ((ν * π)⁻¹) xE) = pv (keyOf r g) := by
    rw [(hRF pv).1 (rinfo ((em zE.1 - 1) / 32) / 128) hr'lt xF (actE ((ν * π)⁻¹) xE) rfl, hfin]
    have key : pv (keyOf r g) = pv (keyOf (rinfo ((em zE.1 - 1) / 32) / 128)
        (labE (rinfo ((em zE.1 - 1) / 32) / 128)
          (actC cmT (piIT.get (rinfo ((em zE.1 - 1) / 32) % 128))
            (actC cmT (ntab ((em zE.1 - 1) % 32)) (x0c r))))) := by
      simpa only [hz] using hsym r hr g hg
    exact_mod_cast key.symm
  have hlab : labE r zE.1 = g := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have hg18 : g < 18 := by rwa [hG.1] at hg
      rw [hz, hG.2.1 g hg18, hR4 g hg18]
    · rw [hz]
      exact ((hG.2.2 r hr hpos).2.1 g hg).2
  have hP3 : Pmat pv xE zE = pv (keyOf r g) := by
    rw [(hRF pv).1 r hr xE zE hx, hlab]
  exact hP3.trans (hP1.trans hP2).symm

/-- **(step 2)** Symmetry in the first row variable: for every row code `x₀_r` and every `y`,
`P (x₀_r, y) = P (y, x₀_r)`. -/
private lemma centralSym (hCF : CodeFacts) (hA : ActSetup) (hRF : RowFacts) (hE : ESem) (hN : NSem)
    (hT : TabSem) (hR : RowSem) (hG : GroupSem)
    (pv : ℕ → ℤ) (hsym : SymHyp pv)
    (r : ℕ) (hr : r < 18) (xE yE : EI) (hx : xE.1 = x0c r) :
    Pmat pv xE yE = Pmat pv yE xE := by
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  have hmul := hA.2.2.2.1
  have hone := hA.2.2.2.2.1
  have hcode := hA.2.2.2.2.2.2.2.1
  have hactinv1 : ∀ σ ∈ Sg, ∀ x : EI, actE σ⁻¹ (actE σ x) = x := by
    intro σ hσ x
    rw [← hmul σ⁻¹ (hSg.2.2 σ hσ) σ hσ x, inv_mul_cancel, hone]
  have hactinv2 : ∀ σ ∈ Sg, ∀ x : EI, actE σ (actE σ⁻¹ x) = x := by
    intro σ hσ x
    rw [← hmul σ hσ σ⁻¹ (hSg.2.2 σ hσ) x, mul_inv_cancel, hone]
  have hPinv : ∀ σ ∈ Sg, ∀ a b : EI, Pmat pv (actE σ a) b = Pmat pv a (actE σ⁻¹ b) := by
    intro σ hσ a b
    have h := (hRF pv).2.1 σ hσ a (actE σ⁻¹ b)
    rwa [hactinv2 σ hσ b] at h
  have hR1 := hR.1
  have hR2 := hR.2.1
  have hR4 := hR.2.2.2.1
  have hR5 := hR.2.2.2.2.1
  have hR7 := hR.2.2.2.2.2.2.1
  have hR8 := hR.2.2.2.2.2.2.2
  have hG1 := hG.1
  have hGgrep0 := hG.2.1
  have hG3 := hG.2.2
  have hgen : ∀ g < ngE r, ∀ zE : EI, zE.1 = grepE r g → Pmat pv xE zE = Pmat pv zE xE :=
    fun g hg zE hz => genSym hCF hA hRF hN hT hR hG pv hsym r hr g hg zE xE hz hx
  have hPxy := (hRF pv).1 r hr xE yE hx
  have hyEmem : yE.1 ∈ eAll := List.mem_toFinset.mp yE.2
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · -- row 0
    subst h0
    have hb0 : labE 0 yE.1 < 18 := hR5 yE.1 hyEmem
    have hb0' : labE 0 yE.1 < ngE 0 := by rw [hG1]; exact hb0
    obtain ⟨-, σ, hσ, y', hy'code, hy'eq⟩ := (hRF pv).2.2 yE
    have hfix : ∀ τ ∈ Sg, actE τ xE = xE := by
      intro τ hτ
      obtain ⟨c, hcvalid, hccode⟩ := hCF.2.1 τ hτ
      rw [← hccode]
      apply Subtype.ext
      show (actE (codeElt c) xE).1 = xE.1
      rw [hcode c hcvalid xE, hx, hR1]
      exact actCode_zero c
    have hPyx : Pmat pv yE xE = Pmat pv y' xE := by
      rw [← hy'eq]
      rw [hPinv σ hσ y' xE, hfix σ⁻¹ (hSg.2.2 σ hσ)]
    have hPy'x : Pmat pv y' xE = Pmat pv xE y' := by
      have hz' : y'.1 = grepE 0 (labE 0 yE.1) := by rw [hy'code, hGgrep0 _ hb0]
      exact (hgen (labE 0 yE.1) hb0' y' hz').symm
    have hPxy' : Pmat pv xE y' = pv (keyOf 0 (labE 0 y'.1)) := (hRF pv).1 0 (by norm_num) xE y' hx
    have hlab' : labE 0 y'.1 = labE 0 yE.1 := by rw [hy'code, hR4 _ hb0]
    rw [hPyx, hPy'x, hPxy', hlab', hPxy]
  · -- row ≥ 1
    obtain ⟨hglt, i, hi, hiy⟩ := (hG3 r hr hpos).1 yE.1 hyEmem
    have hgmem : grepE r (labE r yE.1) ∈ eAll := ((hG3 r hr hpos).2.1 (labE r yE.1) hglt).1
    set zE : EI := ⟨grepE r (labE r yE.1), List.mem_toFinset.mpr hgmem⟩ with hzEdef
    obtain ⟨hvalidc, hlkc⟩ := hR8 r hr hpos i hi
    have hcSg : codeElt ((stabL r).getD i 0) ∈ Sg := (hCF.1 _ hvalidc).1
    have hcmem : (stabL r).getD i 0 ∈ stabL r := getD_mem _ i hi
    have hbounds := hE.2.2.1 (grepE r (labE r yE.1)) hgmem
    have hcy : actE (codeElt ((stabL r).getD i 0)) zE = yE := by
      apply Subtype.ext
      show (actE (codeElt _) zE).1 = yE.1
      rw [hcode _ hvalidc zE]
      show actCode ((stabL r).getD i 0) (grepE r (labE r yE.1)) = yE.1
      rw [actCode_eq_actC ((stabL r).getD i 0) (stabTab r i) (grepE r (labE r yE.1)) hlkc hbounds.1 hbounds.2.1, hiy]
    have hcx : actE (codeElt ((stabL r).getD i 0)) xE = xE := by
      apply Subtype.ext
      show (actE (codeElt _) xE).1 = xE.1
      rw [hcode _ hvalidc xE, hx]
      exact ((hR7 r hr hpos ((stabL r).getD i 0) hvalidc).1).mpr hcmem
    have hσinv : actE (codeElt ((stabL r).getD i 0))⁻¹ xE = xE := by
      calc actE (codeElt ((stabL r).getD i 0))⁻¹ xE
          = actE (codeElt ((stabL r).getD i 0))⁻¹ (actE (codeElt ((stabL r).getD i 0)) xE) := by
              rw [hcx]
        _ = xE := hactinv1 _ hcSg xE
    have hPyx : Pmat pv yE xE = Pmat pv zE xE := by
      rw [← hcy]
      rw [hPinv _ hcSg zE xE, hσinv]
    have hPzx : Pmat pv zE xE = Pmat pv xE zE := (hgen (labE r yE.1) hglt zE rfl).symm
    have hPxe : Pmat pv xE zE = pv (keyOf r (labE r yE.1)) := by
      have h := (hRF pv).1 r hr xE zE hx
      rw [show zE.1 = grepE r (labE r yE.1) from rfl,
        ((hG3 r hr hpos).2.1 (labE r yE.1) hglt).2] at h
      exact h
    rw [hPyx, hPzx, hPxe, hPxy]

theorem symFacts (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts) (hE : ESem)
    (hN : NSem) (hT : TabSem) (hR : RowSem) (hG : GroupSem) : SymFacts := by
  intro pv hsym
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  have hmul := hA.2.2.2.1
  have hone := hA.2.2.2.2.1
  have hactinv2 : ∀ σ ∈ Sg, ∀ x : EI, actE σ (actE σ⁻¹ x) = x := by
    intro σ hσ x
    rw [← hmul σ hσ σ⁻¹ (hSg.2.2 σ hσ) x, mul_inv_cancel, hone]
  have hPinv : ∀ σ ∈ Sg, ∀ a b : EI, Pmat pv (actE σ a) b = Pmat pv a (actE σ⁻¹ b) := by
    intro σ hσ a b
    have h := (hRF pv).2.1 σ hσ a (actE σ⁻¹ b)
    rwa [hactinv2 σ hσ b] at h
  have hcentral : ∀ r < 18, ∀ xE yE : EI, xE.1 = x0c r → Pmat pv xE yE = Pmat pv yE xE :=
    fun r hr xE yE hx => centralSym hCF hA hRF hE hN hT hR hG pv hsym r hr xE yE hx
  have hgen : ∀ a b : EI, Pmat pv a b = Pmat pv b a := by
    intro a b
    obtain ⟨hb, σ, hσ, a', ha'code, ha'eq⟩ := (hRF pv).2.2 a
    have h1 : Pmat pv a b = Pmat pv a' (actE σ⁻¹ b) := by
      rw [← ha'eq]
      exact hPinv σ hσ a' b
    have h2 : Pmat pv a' (actE σ⁻¹ b) = Pmat pv (actE σ⁻¹ b) a' :=
      hcentral (labE 0 a.1) hb a' (actE σ⁻¹ b) ha'code
    have h3 : Pmat pv (actE σ⁻¹ b) a' = Pmat pv b a := by
      have h := (hRF pv).2.1 σ hσ (actE σ⁻¹ b) a'
      rw [hactinv2 σ hσ b, ha'eq] at h
      exact h.symm
    exact h1.trans (h2.trans h3)
  ext a b
  exact hgen b a

end Work.PTCert
