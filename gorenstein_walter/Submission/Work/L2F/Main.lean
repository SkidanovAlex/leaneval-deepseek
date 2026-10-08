/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA L2F : the four model facts, assembled

The four Props of `Submission/Work/L2F/Defs.lean`

* `L2SylowDihedralProp`, `L2InvolutionCentralizerProp`, `L2FourGroupProp`, `L2TIProp`

are proved here for `PSL(2, GF(p,k))`, `p` odd, `p^k ≥ 5`, by specialising the general-field
results of the area (`Submission/Work/L2F/{Mat2,Conic,Involution,Dihedral,PSL,PGL}`).

The main theorems of this file are `Work.L2F.l2SylowDihedral`, `Work.L2F.l2InvolutionCentralizer`,
`Work.L2F.l2FourGroup` and `Work.L2F.l2TI`; each *is* the corresponding Prop.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.circle_card
import Submission.Work.L2F.Conic.ncard_squares
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Involution.lift_sq_neg_one
import Submission.Work.L2F.PSL.centralizer_psl_dihedral
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.PSL.pslUnipotent_pow
import Submission.Work.L2F.PSL.pslSplitTorus_card
import Submission.Work.L2F.PSL.pslSplitTorus_isCyclic
import Submission.Work.L2F.PSL.pslHypTorus_card
import Submission.Work.L2F.PSL.pslHypTorus_cyclic
import Submission.Work.L2F.PSL.normalizer_pslUnipotent_card
import Submission.Work.L2F.PSL.normalizer_pslSplitTorus_dihedral
import Submission.Work.L2F.PSL.normalizer_pslHypTorus_dihedral
import Submission.Work.L2F.PSL.ti_pslUnipotent
import Submission.Work.L2F.PSL.ti_pslSplitTorus
import Submission.Work.L2F.PSL.ti_pslHypTorus
import Submission.Work.L2F.PSL.centralizer_fourGroup_psl
import Submission.Work.L2F.PSL.sylow_psl_dihedral
import Submission.Work.L2F.PGL.centralizer_fourGroup
import Submission.Work.PSL2.Card

open scoped MatrixGroups
open Matrix
open Subgroup (centralizer normalizer zpowers)

namespace Work.L2F

/-! ## The `GF(p,k)` set-up

For `p` an odd prime and `5 ≤ p^k` the field `GF(p,k)` has odd characteristic, and we record the
elementary consequences we need below. -/

section Galois

/-- `k ≠ 0` follows from `5 ≤ p^k`. -/
theorem ne_zero_of_five_le {p k : ℕ} (hk : 5 ≤ p ^ k) : k ≠ 0 := by
  rintro rfl
  simp at hk

/-- `2 ≠ 0` in `GF(p,k)` for `p` odd. -/
theorem two_ne_zero_galois {p k : ℕ} [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p k) ≠ 0 := by
  haveI : CharP (GaloisField p k) p := inferInstance
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p = 2 := le_antisymm hle hge
  obtain ⟨m, hm⟩ := hp
  omega

/-- The cardinality of `GF(p,k)`. -/
theorem card_galois {p k : ℕ} [Fact p.Prime] (hk : 5 ≤ p ^ k) :
    Nat.card (GaloisField p k) = p ^ k :=
  GaloisField.card p k (ne_zero_of_five_le hk)

/-- `5 ≤ Nat.card (GF(p,k))`. -/
theorem five_le_card_galois {p k : ℕ} [Fact p.Prime] (hk : 5 ≤ p ^ k) :
    5 ≤ Nat.card (GaloisField p k) := by
  rw [card_galois hk]; exact hk

/-- There is a nonzero non-square in `GF(p,k)` (`p` odd, `5 ≤ p^k`). -/
theorem exists_nonsquare_galois {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    ∃ d : GaloisField p k, d ≠ 0 ∧ ∀ a : GaloisField p k, a * a ≠ d := by
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard := card_galois hk
  have ex : ∃ d : GaloisField p k, ∀ a : GaloisField p k, a * a ≠ d := by
    by_contra h
    push Not at h
    have hsub : {x : GaloisField p k | IsSquare x} = Set.univ := by
      ext x
      constructor
      · exact fun _ => Set.mem_univ x
      · intro _
        obtain ⟨a, ha⟩ := h x
        exact ⟨a, ha.symm⟩
    have hcount : {x : GaloisField p k | IsSquare x}.ncard = Nat.card (GaloisField p k) := by
      rw [hsub, Set.ncard_univ, Nat.card_eq_fintype_card]
    have hn := Conic.ncard_squares (GaloisField p k) (two_ne_zero_galois hp)
    rw [hn] at hcount
    rw [hcard] at hcount
    have hodd : Odd (p ^ k) := hp.pow
    omega
  obtain ⟨d, hd⟩ := ex
  refine ⟨d, ?_, hd⟩
  rintro rfl
  exact hd 0 (by ring)

end Galois

/-! ## The four Props -/

/-- **L2F.1** `L2SylowDihedralProp`. -/
theorem l2SylowDihedral : L2SylowDihedralProp := by
  intro p k _ hp hk S
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  exact PSL.sylow_psl_dihedral (GaloisField p k) (two_ne_zero_galois (k := k) hp)
    (five_le_card_galois (p := p) hk) S

/-- **L2F.2** `L2InvolutionCentralizerProp`. -/
theorem l2InvolutionCentralizer : L2InvolutionCentralizerProp := by
  intro p k _ hp hk t ht
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 := two_ne_zero_galois (k := k) hp
  have hcard := card_galois (p := p) hk
  obtain ⟨x, hx, hx2⟩ := Involution.lift_sq_neg_one (GaloisField p k) h2 t ht
  obtain ⟨n, hn, hiso⟩ := PSL.centralizer_psl_dihedral (GaloisField p k) h2 x hx2
  refine ⟨n, ⟨?_, ?_⟩⟩
  · rcases Conic.circle_card (GaloisField p k) h2 with h | h
    · left; rw [hn, h, hcard]
    · right; rw [hn, h, hcard]
  · rw [← hx]; exact hiso

/-- **L2F.3** `L2FourGroupProp`. -/
theorem l2FourGroup : L2FourGroupProp := by
  intro p k _ hp hk
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 := two_ne_zero_galois (k := k) hp
  exact ⟨fun V hV => PSL.centralizer_fourGroup_psl (GaloisField p k) h2 V hV,
    fun V hV => PGL.centralizer_fourGroup (GaloisField p k) h2 V hV⟩

/-- **L2F.4** `L2TIProp`. -/
theorem l2TI : L2TIProp := by
  intro p k _ hp hk
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 := two_ne_zero_galois (k := k) hp
  have hcard := card_galois (p := p) hk
  have h5 := five_le_card_galois (p := p) hk
  obtain ⟨d, hd0, hdns⟩ := exists_nonsquare_galois hp hk
  refine ⟨pslUnipotent (GaloisField p k), pslHypTorus (GaloisField p k) d,
    pslSplitTorus (GaloisField p k), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PSL.pslUnipotent_card (GaloisField p k) h2, hcard]
  · rw [PSL.pslHypTorus_card (GaloisField p k) h2 d hd0 hdns, hcard]
  · rw [PSL.pslSplitTorus_card (GaloisField p k) h2, hcard]
  · exact PSL.pslHypTorus_cyclic (GaloisField p k) h2 d hd0
  · exact PSL.pslSplitTorus_isCyclic (GaloisField p k)
  · intro x hx
    exact PSL.pslUnipotent_pow (GaloisField p k) p (inferInstance : CharP (GaloisField p k) p) x hx
  · intro g hg
    exact PSL.ti_pslUnipotent (GaloisField p k) h2 g hg
  · intro g hg
    exact PSL.ti_pslHypTorus (GaloisField p k) h2 d hd0 g hg
  · intro g hg
    exact PSL.ti_pslSplitTorus (GaloisField p k) h2 g hg
  · rw [PSL.normalizer_pslUnipotent_card (GaloisField p k) h2, hcard]
  · exact PSL.normalizer_pslHypTorus_dihedral (GaloisField p k) h2 h5 d hd0 hdns
  · exact PSL.normalizer_pslSplitTorus_dihedral (GaloisField p k) h2 h5

end Work.L2F
