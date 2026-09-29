import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtLabSetupAux
import Submission.Work.MainP.crtLabSetup
import Submission.Work.MainP.crtLabLoop
import Submission.Work.MainP.crtLabEpiM

/-!
# `crtLabWord`: computing `sigmaList ss` on the value stack

Assembly of the three phases of the "label and sort" word of the CRT reindexing (paper Prop. 5.4,
step 2, the part producing the label list):

* `Work.MainP.crtLabSetup` : `int S :: intList ss`  ↦  `ofList (drv S) :: acc ss 0`
* `Work.MainP.crtLabLoop`  : `S` odometer steps     ↦  `acc ss S`
* `Work.MainP.crtLabEpiM`  : label extraction       ↦  `intList (sigmaList ss)`

with the costs

* `Kset * (vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + S + 1)`,
* `Klo * (S * (ss.length + 1) * (S.size + 2) + 1)` and the same for `Kep`,

absorbed into the target bound `K * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1)` using only
`ss.length + 1 ≤ vsz (intList ss)`, `1 ≤ S` and `(S.size + 2) ≤ 2 * (S.size + 1)`; see
`crtLabCostFinal`.  The single constant is `4 * Kset + 2 * Klo + 2 * Kep`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Elementary size bound -/

/-- The list bound: `ss.length + 1 ≤ vsz (intList ss)`. -/
theorem length_le_vsz_intList (ss : List ℕ) : ss.length + 1 ≤ vsz (intList ss) := by
  rw [vsz_intList]
  have := Nat.zero_le ((ss.map iszN).sum)
  omega

/-! ## Cost arithmetic -/

/-- The arithmetic absorbing the three phase costs into the target bound.

`d = vsz (intList ss)`, `L = ss.length`, `sz = S.size`, `S ≥ 1` and `L + 1 ≤ d`. -/
theorem crtLabCostFinal (Kset Klo Kep S L d sz : ℕ) (hS : 1 ≤ S) (hL : L + 1 ≤ d) :
    Kset * (d * (sz + 1) + (L + 1) * (sz + 1) + S + 1)
      + (Klo * (S * (L + 1) * (sz + 2) + 1) + Kep * (S * (L + 1) * (sz + 2) + 1))
    ≤ (4 * Kset + 2 * Klo + 2 * Kep) * (S * (d + 1) * (sz + 1) + 1) := by
  set T : ℕ := S * (d + 1) * (sz + 1) + 1 with hT
  -- the atom bounds
  have hUW : d * (sz + 1) ≤ (d + 1) * (sz + 1) := Nat.mul_le_mul (by omega) (le_refl _)
  have hVU : (L + 1) * (sz + 1) ≤ d * (sz + 1) := Nat.mul_le_mul hL (le_refl _)
  have hW1 : 1 ≤ (d + 1) * (sz + 1) := by
    have := Nat.mul_pos (show 0 < d + 1 by omega) (show 0 < sz + 1 by omega)
    omega
  have hWW : (d + 1) * (sz + 1) ≤ S * (d + 1) * (sz + 1) := by
    calc (d + 1) * (sz + 1) = 1 * ((d + 1) * (sz + 1)) := (one_mul _).symm
      _ ≤ S * ((d + 1) * (sz + 1)) := Nat.mul_le_mul hS (le_refl _)
      _ = S * (d + 1) * (sz + 1) := by ring
  have hSR : S ≤ S * (d + 1) * (sz + 1) := by
    calc S = S * 1 := (Nat.mul_one S).symm
      _ ≤ S * ((d + 1) * (sz + 1)) := Nat.mul_le_mul (le_refl _) hW1
      _ = S * (d + 1) * (sz + 1) := by ring
  have hA : d * (sz + 1) + (L + 1) * (sz + 1) + S + 1 ≤ 4 * T := by
    rw [hT]
    omega
  have h2 : (L + 1) * (sz + 2) ≤ 2 * ((d + 1) * (sz + 1)) := by
    have hsz : sz + 2 ≤ 2 * (sz + 1) := by omega
    calc (L + 1) * (sz + 2) ≤ d * (sz + 2) := Nat.mul_le_mul hL (le_refl _)
      _ ≤ d * (2 * (sz + 1)) := Nat.mul_le_mul (le_refl _) hsz
      _ = 2 * (d * (sz + 1)) := by ring
      _ ≤ 2 * ((d + 1) * (sz + 1)) := Nat.mul_le_mul (le_refl _) hUW
  have hB : S * (L + 1) * (sz + 2) + 1 ≤ 2 * T := by
    rw [hT]
    have h3 : S * (L + 1) * (sz + 2) ≤ 2 * (S * (d + 1) * (sz + 1)) := by
      calc S * (L + 1) * (sz + 2) = S * ((L + 1) * (sz + 2)) := by ring
        _ ≤ S * (2 * ((d + 1) * (sz + 1))) := Nat.mul_le_mul (le_refl _) h2
        _ = 2 * (S * (d + 1) * (sz + 1)) := by ring
    omega
  have hcs : Kset * (d * (sz + 1) + (L + 1) * (sz + 1) + S + 1) ≤ Kset * (4 * T) :=
    Nat.mul_le_mul (le_refl _) hA
  have hcl : Klo * (S * (L + 1) * (sz + 2) + 1) ≤ Klo * (2 * T) :=
    Nat.mul_le_mul (le_refl _) hB
  have hce : Kep * (S * (L + 1) * (sz + 2) + 1) ≤ Kep * (2 * T) :=
    Nat.mul_le_mul (le_refl _) hB
  calc Kset * (d * (sz + 1) + (L + 1) * (sz + 1) + S + 1)
        + (Klo * (S * (L + 1) * (sz + 2) + 1) + Kep * (S * (L + 1) * (sz + 2) + 1))
      ≤ Kset * (4 * T) + (Klo * (2 * T) + Kep * (2 * T)) :=
        Nat.add_le_add hcs (Nat.add_le_add hcl hce)
    _ = (4 * Kset + 2 * Klo + 2 * Kep) * T := by ring

/-! ## The target theorem -/

theorem crtLabWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    HvdH.WordR main prog
      (fun vs => ∃ rest, vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest)
      (fun vs out => ∃ rest, vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest ∧
        out = HvdH.intList (Work.MainP.sigmaList ss) :: rest)
      (fun _ => K * (S * (HvdH.vsz (HvdH.intList ss) + 1) * (S.size + 1) + 1)) := by
  obtain ⟨setP, Kset, hset⟩ := crtLabSetup hK hI hL
  obtain ⟨loopP, Klo, hloop⟩ := crtLabLoop hK hI
  obtain ⟨epiP, Kep, hepi⟩ := crtLabEpiM hK hL
  refine ⟨setP.seq (loopP.seq epiP), 4 * Kset + 2 * Klo + 2 * Kep, ?_⟩
  intro main ss S hpos hS
  have hS1 : 1 ≤ S := by rw [hS]; exact List.one_le_prod (fun x hx => hpos x hx)
  have hlen : ss.length + 1 ≤ vsz (intList ss) := length_le_vsz_intList ss
  -- the three phases, with the ambient tail made explicit
  have h1 : ∀ rest, WordR main setP
      (fun vs => vs = .int (S : ℤ) :: intList ss :: rest)
      (fun _ out => out = ofList (drv S) :: acc ss 0 :: rest)
      (fun _ => Kset * (vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1)
        + S + 1)) :=
    fun rest => epiWrdFix (L0 := [.int (S : ℤ), intList ss]) (L1 := [ofList (drv S), acc ss 0])
      (hset main ss S hpos hS) le_rfl rest
  have h2 : ∀ rest, WordR main loopP
      (fun vs => vs = ofList (drv S) :: acc ss 0 :: rest)
      (fun _ out => out = acc ss S :: rest)
      (fun _ => Klo * (S * (ss.length + 1) * (S.size + 2) + 1)) := by
    intro rest
    refine Work.Kernel.WordR_conseq (hloop main ss S rest hpos hS)
      (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
    intro vs out hvs hq
    exact hq.2
  have h3 : ∀ rest, WordR main epiP
      (fun vs => vs = acc ss S :: rest)
      (fun _ out => out = intList (sigmaList ss) :: rest)
      (fun _ => Kep * (S * (ss.length + 1) * (S.size + 2) + 1)) := by
    intro rest
    refine Work.Kernel.WordR_conseq (hepi main ss S rest hpos hS)
      (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
    intro vs out hvs hq
    exact hq.2
  -- the chain, and the cost
  refine wordR_exists_tail (fun tl => .int (S : ℤ) :: intList ss :: tl)
    (fun tl => intList (sigmaList ss) :: tl)
    ((4 * Kset + 2 * Klo + 2 * Kep) * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1)) ?_
  intro rest
  refine Work.Kernel.WordR_conseq
    (wordR_seqC hK (h1 rest) (wordR_seqC hK (h2 rest) (h3 rest)))
    (fun vs hvs => hvs) (fun vs out _ hq => hq) ?_
  intro vs _
  exact crtLabCostFinal Kset Klo Kep S ss.length (vsz (intList ss)) S.size hS1 hlen

end Work.MainP
