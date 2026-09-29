import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Params.defs
import Submission.Work.Params.sizearith
import Submission.Work.Params.progaux
import Submission.Work.Params.constSizesBig
import Submission.Work.Params.parSizesBig
import Submission.Work.Params.listSizesBig
import Submission.Work.Params.n1SizeBig
import Submission.Work.Params.steps
import Submission.Work.Params.paramok
import Submission.Work.Params.rparbig
import Submission.Work.Main.defs
import Submission.Work.Params.V_le_pow

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000


namespace Work.Params

open HvdH

example (SB : ℕ) : ((SB + (SB + SB)) + ((SB + SB) + (SB + SB))) ≤ 7 * SB := (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 3 4 SB))))

/-- Final cost bound of the `Params` program (proved in a small context, so that no
tactic ever has to unfold `K0 = Ksum + 2 ^ 44 + 100`, which would be catastrophic). -/
theorem cost_bound {B W SB K0 m : ℕ} (hB : 2 ≤ B) (hW : W = B ^ K0) (hSB : SB = W ^ 40)
    (hK0 : 1 ≤ K0) (hm : m ≤ 78 * SB) : m ≤ (65536 * K0) * B ^ (65536 * K0) := by
  have hB0 : 0 < B := by omega
  have hK00 : 0 < K0 := by omega
  have h1 : W ^ 40 = B ^ (K0 * 40) := by rw [hW]; exact (Nat.pow_mul B K0 40).symm
  have h2 : B ^ (K0 * 40) ≤ B ^ (65536 * K0) :=
    Nat.pow_le_pow_right hB0 (show K0 * 40 ≤ 65536 * K0 by omega)
  have h4 : 78 * B ^ (65536 * K0) ≤ (65536 * K0) * B ^ (65536 * K0) :=
    Nat.mul_le_mul_right _ (show (78:ℕ) ≤ 65536 * K0 by omega)
  calc m ≤ 78 * SB := hm
    _ = 78 * W ^ 40 := by rw [hSB]
    _ = 78 * B ^ (K0 * 40) := by rw [h1]
    _ ≤ 78 * B ^ (65536 * K0) := Nat.mul_le_mul_left 78 h2
    _ ≤ (65536 * K0) * B ^ (65536 * K0) := h4
theorem seg1
    (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (main : Cmd) (n : ℕ) (R : List Val)
    (dupP : Cmd)
    (Kdup : ℕ)
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest) (fun vs => Kdup * (vsz (vs.headD .nil) + 1)))
    (dropP : Cmd)
    (Kdrop : ℕ)
    (hdrop : ∀ main : Cmd, WordR main dropP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest) (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (swapP : Cmd)
    (Kswap : ℕ)
    (hswap : ∀ main : Cmd, WordR main swapP (fun vs => 2 ≤ vs.length) (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest) (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (pickP : ℕ → Cmd)
    (Kpick : ℕ)
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs) (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (rollP : ℕ → Cmd)
    (Kroll : ℕ)
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k) (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (pushP : Val → Cmd)
    (Kpush : ℕ)
    (hpush : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs) (fun _ => Kpush * (vsz v + 1)))
    (ifZeroP : Cmd → Cmd → Cmd)
    (KifZero : ℕ)
    (hifZero : ∀ (main q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ), (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) → (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) → WordR main (ifZeroP q₁ q₂) (fun vs => vs = .int z :: rest) (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => KifZero * (isz z + 1) + max c₁ c₂))
    (mapListP : Cmd → Cmd)
    (KmapList : ℕ)
    (hmapList : ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ), (∀ x : Val, P x → WordR main q (fun vs => vs = x :: rest) (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) → ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) → WordR main (mapListP q) (fun vs => vs = ofList xs :: rest) (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys) (fun _ => xs.length * (c + KmapList * (L + 1)) + KmapList))
    (addP : Cmd)
    (Kadd : ℕ)
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (fun a b => a + b) (fun a b => Kadd * (isz a + isz b)))
    (subP : Cmd)
    (Ksub : ℕ)
    (hsub : ∀ main : Cmd, BinOp main subP (fun _ _ => True) (fun a b => a - b) (fun a b => Ksub * (isz a + isz b)))
    (negP : Cmd)
    (Kneg : ℕ)
    (hneg : ∀ main : Cmd, UnOp main negP (fun _ => True) (fun a => -a) (fun a => Kneg * isz a))
    (ltP : Cmd)
    (Klt : ℕ)
    (hlt : ∀ main : Cmd, BinOp main ltP (fun _ _ => True) (fun a b => if a < b then 1 else 0) (fun a b => Klt * (isz a + isz b)))
    (mulSP : Cmd)
    (KmulS : ℕ)
    (hmulS : ∀ main : Cmd, BinOp main mulSP (fun _ _ => True) (fun a b => a * b) (fun a b => KmulS * isz a * isz b))
    (fdivP : Cmd)
    (Kfdiv : ℕ)
    (hfdiv : ∀ main : Cmd, BinOp main fdivP (fun a b => 0 < b) Int.fdiv (fun a b => Kfdiv * isz a * isz b))
    (sqrtP : Cmd)
    (Ksqrt : ℕ)
    (hsqrt : ∀ main : Cmd, UnOp main sqrtP (fun a => 0 ≤ a) (fun a => ↑a.toNat.sqrt) (fun a => Ksqrt * isz a ^ 2))
    (clog2P : Cmd)
    (Kclog2 : ℕ)
    (hclog2 : ∀ main : Cmd, UnOp main clog2P (fun a => 0 ≤ a) (fun a => ↑(Nat.clog 2 a.toNat)) (fun a => Kclog2 * isz a))
    (pow2P : Cmd)
    (Kpow2 : ℕ)
    (hpow2 : ∀ main : Cmd, UnOp main pow2P (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat) (fun k => Kpow2 * (k.toNat + isz k)))
    (Ksum K0 B W V SB : ℕ)
    (hKsumdef : Ksum = Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + KifZero + KmapList + Kadd + Ksub + Kneg + Klt + KmulS + Kfdiv + Ksqrt + Kclog2 + Kpow2)
    (hK0def : K0 = Ksum + 2 ^ 44 + 100)
    (hBdef : B = n.size + 1)
    (hVdef : V = (KBsz + n.size + 6) * (D + 2))
    (hWdef : W = B ^ K0)
    (hSBdef : SB = W ^ 40)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hsz : 65755586 ≤ n.size)
    (hn2 : 1 < n)
    (hK0pos : 1 ≤ K0)
    (hK0ge : 2 ^ 44 + 100 ≤ K0)
    (hB2 : 2 ≤ B)
    (hVdef2 : V = (KBsz + n.size + 6) * (D + 2))
    (hW2 : 2 ≤ W)
    (hW4 : 4 ≤ W)
    (hW100 : 100 ≤ W)
    (hVW : V + 1 ≤ W)
    (hVsz : n.size + 100 ≤ V)
    (hK0W : K0 ≤ W)
    (hKdupW : Kdup ≤ W)
    (hKdropW : Kdrop ≤ W)
    (hKswapW : Kswap ≤ W)
    (hKpickW : Kpick ≤ W)
    (hKrollW : Kroll ≤ W)
    (hKpushW : Kpush ≤ W)
    (hKifZeroW : KifZero ≤ W)
    (hKmapListW : KmapList ≤ W)
    (hKaddW : Kadd ≤ W)
    (hKsubW : Ksub ≤ W)
    (hKnegW : Kneg ≤ W)
    (hKltW : Klt ≤ W)
    (hKmulSW : KmulS ≤ W)
    (hKfdivW : Kfdiv ≤ W)
    (hKsqrtW : Ksqrt ≤ W)
    (hKclog2W : Kclog2 ≤ W)
    (hKpow2W : Kpow2 ≤ W)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hW77 : 77 ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hSB20 : W ^ 20 ≤ SB)
    (hSB30 : W ^ 20 ≤ W ^ 30)
    (hSB34 : W ^ 34 ≤ W ^ 34)
    (hSB37 : W ^ 37 ≤ SB)
    (hbparT : (bpar n).size ≤ n.size + 4)
    (hpparT : (ppar n).size ≤ n.size + 4)
    (haparT : (apar n).size ≤ n.size + 4)
    (hkTparT : (kTpar n).size ≤ n.size + 4)
    (hTparT : (Tpar n).size ≤ n.size + 4)
    (hkrparT : (krpar n).size ≤ n.size + 4)
    (hrparT : (rpar n).size ≤ n.size + 4)
    (hdparT : (dpar n).size ≤ n.size + 4)
    (hLparT : (Lpar n).size ≤ n.size + 4)
    (huparT : (upar n).size ≤ n.size + 4)
    (hNsz : n.size ≤ n.size + 50)
    (hbpar : (bpar n).size ≤ n.size + 50)
    (hppar : (ppar n).size ≤ n.size + 50)
    (hapar : (apar n).size ≤ n.size + 50)
    (hkTpar : (kTpar n).size ≤ n.size + 50)
    (hTpar : (Tpar n).size ≤ n.size + 50)
    (hkrpar : (krpar n).size ≤ n.size + 50)
    (hrpar : (rpar n).size ≤ n.size + 50)
    (hdpar : (dpar n).size ≤ n.size + 50)
    (hLpar : (Lpar n).size ≤ n.size + 50)
    (hupar : (upar n).size ≤ n.size + 50)
    (hupar4 : (upar n).size ≤ n.size + 4)
    (h6c : (6:ℕ).size ≤ n.size + 50)
    (h1 : (1:ℕ).size ≤ n.size + 50)
    (h2c : (2:ℕ).size ≤ n.size + 50)
    (h4c : (4:ℕ).size ≤ n.size + 50)
    (hD : (D:ℕ).size ≤ n.size + 50)
    (hDv : (D:ℕ).size ≤ 11)
    (hDm1 : (D - 1).size ≤ n.size + 50)
    (h2Dm1v : (2 * D - 1).size ≤ 13)
    (h2Dm1 : (2 * D - 1).size ≤ n.size + 50)
    (h4Dv : (4 * D).size ≤ 14)
    (h4D : (4 * D).size ≤ n.size + 50)
    (hFfacT : (Ffac).size ≤ n.size + 4)
    (hQallT : (Qall).size ≤ n.size + 4)
    (hFfac : (Ffac).size ≤ n.size + 50)
    (hFfac4 : (Ffac).size ≤ n.size + 4)
    (hQall : (Qall).size ≤ n.size + 50)
    (hFQ3 : (Ffac * Qall).size ≤ n.size + 4)
    (hFQ : (Ffac * Qall).size ≤ n.size + 50)
    (hK13 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hK1 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (h2Fv : (2 * Ffac).size ≤ n.size + 4)
    (h2F : (2 * Ffac).size ≤ n.size + 50)
    (h2F4 : (2 * Ffac).size ≤ n.size + 4)
    (hDD : (12 * D * D).size ≤ 26)
    (hDDbT : (12 * D * D * bpar n).size ≤ n.size + 30)
    (hDDb : (12 * D * D * bpar n).size ≤ n.size + 50)
    (hDDb1 : (12 * D * D * bpar n - 1).size ≤ n.size + 50)
    (hSQ1 : (Nat.sqrt (12 * D * D * bpar n - 1)).size ≤ n.size + 50)
    (hSQ2 : (Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1))).size ≤ n.size + 50)
    (hN4T : (4 * n).size ≤ n.size + 3)
    (hN4 : (4 * n).size ≤ n.size + 50)
    (hN4bT : (4 * n + bpar n).size ≤ n.size + 5)
    (hN4b : (4 * n + bpar n).size ≤ n.size + 50)
    (hN4b1 : (4 * n + bpar n - 1).size ≤ n.size + 50)
    (hQVT : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 5)
    (hQV : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 50)
    (hDKRT : (D * krpar n).size ≤ n.size + 20)
    (hDKR : (D * krpar n).size ≤ n.size + 50)
    (hR2D1T : (rpar n * (2 * D - 1)).size ≤ n.size + 20)
    (hR2D1 : (rpar n * (2 * D - 1)).size ≤ n.size + 50)
    (hR4D : (rpar n * (2 * D - 1) / (4 * D)).size ≤ n.size + 50)
    (hLK1T : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 5)
    (hLK1 : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (hMMT : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 5)
    (hMM : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 50)
    (hMFQ : (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall)).size ≤ n.size + 50)
    (hVLD : vsz (HvdH.intList (List.range D)) ≤ V)
    (hVss : vsz (HvdH.intList (ssPar n)) ≤ V)
    (hVts : vsz (HvdH.intList (tsPar n)) ≤ V)
    (hVLD2 : vsz (intList2 (List.range D)) ≤ V)
    (hVssl : vsz (intList2 (ssPar n)) ≤ V)
    (hVtsl : vsz (intList2 (tsPar n)) ≤ V)
    (hDleW : D ≤ W)
    (hbparposN : 0 < bpar n)
    (hkTw : kTpar n ≤ W)
    (hkrw : krpar n ≤ W)
    (hLpos : 0 < Lpar n)
    (huparpos : 0 < upar n)
    (hposDDb : 0 < 12 * D * D * bpar n)
    (hposN4b : 0 < 4 * n + bpar n)
    (hneg1isz : isz (-1 : ℤ) ≤ W)
    (Hbparpos : (0:ℤ) < (bpar n : ℤ))
    (Hdpos : (0:ℤ) < (D : ℤ))
    (H4Dpos : (0:ℤ) < (4 * D : ℤ))
    (HFQpos : (0:ℤ) < (Ffac * Qall : ℤ))
    (hDle : HvdH.D ≤ 2 ^ 11)
    (hVs26 : (26:ℕ) + 2 ≤ V)
    (hVs51 : n.size + 50 + 1 + 2 ≤ V)
    (hVs11 : (11:ℕ) + 2 ≤ V)
    (hVs12 : (12:ℕ) + 2 ≤ V)
    (hVs24 : ((n.size + 4) + 2) + 2 ≤ V)
    (hVsFk : ((n.size + 4) + 12) + 2 ≤ V)
    (hVsUk : (((n.size + 4) + 12) + 1) + 2 ≤ V)
    (hVs50 : n.size + 50 + 2 ≤ V)
    (hVWle : V ≤ W)
    (hWs26 : (26:ℕ) + 2 ≤ W)
    (hWs51 : n.size + 50 + 1 + 2 ≤ W)
    (hWs11 : (11:ℕ) + 2 ≤ W)
    (hWs12 : (12:ℕ) + 2 ≤ W)
    (hWs24 : ((n.size + 4) + 2) + 2 ≤ W)
    (hWsFk : ((n.size + 4) + 12) + 2 ≤ W)
    (hWsUk : (((n.size + 4) + 12) + 1) + 2 ≤ W)
    (hWs50 : n.size + 50 + 2 ≤ W)
    (hc6 : Nat.size 6 ≤ n.size + 4)
    (hcDD : (12 * D * D).size ≤ n.size + 4)
    (hc1 : Nat.size 1 ≤ n.size + 4)
    (hc4 : Nat.size 4 ≤ n.size + 4)
    (hcDm1 : (D - 1).size ≤ n.size + 4)
    (hcDz : D.size ≤ n.size + 4)
    (hc2Dm1 : (2 * D - 1).size ≤ n.size + 4)
    (hc4D : (4 * D).size ≤ n.size + 4)
    (hcF : Ffac.size ≤ n.size + 4)
    (hcQ : Qall.size ≤ n.size + 4)
    (hcFQ : (Ffac * Qall).size ≤ n.size + 4)
    (hcK1z : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hc2F : (2 * Ffac).size ≤ n.size + 4)
    :
    WordR main (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) (clog2P)) (Cmd.seq (dupP) ((pushP (.int ((6 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pickP 1))) (Cmd.seq ((pushP (.int ((12 * D * D : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq ((pushP (.int (-1 : ℤ)))) (addP)) (Cmd.seq (sqrtP) (sqrtP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pickP 3)) ((pushP (.int ((4 : ℕ) : ℤ)))))))) (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (mulSP) ((pickP 3))) (Cmd.seq (addP) ((pushP (.int (-1 : ℤ)))))) (Cmd.seq (Cmd.seq (addP) ((pickP 3))) (Cmd.seq (swapP) (fdivP)))) (Cmd.seq (Cmd.seq (Cmd.seq (clog2P) (dupP)) (Cmd.seq (pow2P) ((pickP 1)))) (Cmd.seq (Cmd.seq ((pushP (.int ((D - 1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((D : ℕ) : ℤ)))) (swapP)))))) (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (fdivP) (dupP)) (Cmd.seq (pow2P) ((pickP 1)))) (Cmd.seq (Cmd.seq ((pushP (.int ((D : ℕ) : ℤ)))) (mulSP)) (Cmd.seq ((pickP 4)) (negP)))) (Cmd.seq (Cmd.seq (Cmd.seq (addP) ((rollP 2))) (Cmd.seq (dropP) ((rollP 3)))) (Cmd.seq (Cmd.seq (dropP) ((rollP 6))) (Cmd.seq (dropP) ((pickP 1)))))) (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq ((pushP (.int (((2 * D - 1) : ℕ) : ℤ)))) (mulSP)) (Cmd.seq ((pushP (.int (((4 * D) : ℕ) : ℤ)))) (swapP))) (Cmd.seq (Cmd.seq (fdivP) ((pushP (.int ((1 : ℕ) : ℤ))))) (Cmd.seq (addP) ((pushP (.int ((Ffac * Qall - 1 - Qall : ℕ) : ℤ))))))) (Cmd.seq (Cmd.seq (Cmd.seq (addP) ((pushP (.int ((Ffac * Qall : ℕ) : ℤ))))) (Cmd.seq (swapP) (fdivP))) (Cmd.seq (Cmd.seq ((pushP (.int ((Ffac * Qall : ℕ) : ℤ)))) (mulSP)) (Cmd.seq ((pushP (.int ((Qall : ℕ) : ℤ)))) (addP))))))) (fun vs => vs = .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((upar n : ℕ) : ℤ) :: .int ((dpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((bpar n : ℕ) : ℤ) :: R) (fun _ => 64 * SB) := by
  let v1 : Val := .int ((bpar n : ℕ) : ℤ)
  let v2 : Val := .int ((ppar n : ℕ) : ℤ)
  let v3 : Val := .int ((12 * D * D : ℕ) : ℤ)
  let v4 : Val := .int ((12 * D * D * bpar n : ℕ) : ℤ)
  let v5 : Val := .int ((12 * D * D * bpar n - 1 : ℕ) : ℤ)
  let v6 : Val := .int ((Nat.sqrt (12 * D * D * bpar n - 1) : ℕ) : ℤ)
  let v7 : Val := .int ((Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1)) : ℕ) : ℤ)
  let v8 : Val := .int ((apar n : ℕ) : ℤ)
  let v9 : Val := .int ((4 * n : ℕ) : ℤ)
  let v10 : Val := .int ((4 * n + bpar n : ℕ) : ℤ)
  let v11 : Val := .int ((4 * n + bpar n - 1 : ℕ) : ℤ)
  let v12 : Val := .int (((4 * n + bpar n - 1) / bpar n : ℕ) : ℤ)
  let v13 : Val := .int ((kTpar n : ℕ) : ℤ)
  let v14 : Val := .int ((Tpar n : ℕ) : ℤ)
  let v15 : Val := .int ((D - 1 : ℕ) : ℤ)
  let v16 : Val := .int ((kTpar n + (D - 1) : ℕ) : ℤ)
  let v17 : Val := .int ((krpar n : ℕ) : ℤ)
  let v18 : Val := .int ((rpar n : ℕ) : ℤ)
  let v19 : Val := .int ((D * krpar n : ℕ) : ℤ)
  let v20 : Val := .int ((dpar n : ℕ) : ℤ)
  let v21 : Val := .int (((2 * D - 1) : ℕ) : ℤ)
  let v22 : Val := .int ((rpar n * (2 * D - 1) : ℕ) : ℤ)
  let v23 : Val := .int (((4 * D) : ℕ) : ℤ)
  let v24 : Val := .int ((rpar n * (2 * D - 1) / (4 * D) : ℕ) : ℤ)
  let v25 : Val := .int ((Lpar n : ℕ) : ℤ)
  let v26 : Val := .int ((Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v27 : Val := .int ((Lpar n + Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v28 : Val := .int ((Ffac * Qall : ℕ) : ℤ)
  let v29 : Val := .int (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall) : ℕ) : ℤ)
  let v30 : Val := .int ((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall) : ℕ) : ℤ)
  let v31 : Val := .int ((Qall : ℕ) : ℤ)
  let v32 : Val := .int ((upar n : ℕ) : ℤ)
  have H1 : WordR main _ (fun vs => vs = .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((n : ℕ) : ℤ) :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    dupStep hK (hdup main) (.int ((n : ℕ) : ℤ)) (R) (SB) (cost1 hW2 hSB20 hKdup (vszV (hNsz) hVs50) hVW)
  have H2 : WordR main _ (fun vs => vs = .int ((n : ℕ) : ℤ) :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hclog2 main) (((n : ℕ) : ℤ)) (.int ((n : ℕ) : ℤ) :: R) (znonneg (n)) (((bpar n : ℕ) : ℤ)) (by rw [Int.toNat_natCast, HvdH.bpar]) (SB) (cost9 hW2 hSB20 hKclog2 (iszV (hNsz) hWs50))
  have H3 : WordR main _ (fun vs => vs = v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v1 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    dupStep hK (hdup main) (v1) (.int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKdup (vszV (hbpar) hVs50) hVW)
  have H4 : WordR main _ (fun vs => vs = v1 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((6 : ℕ) : ℤ) :: v1 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int ((6 : ℕ) : ℤ)) (v1 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (h6c) hVs50) hVW)
  have H5 : WordR main _ (fun vs => vs = .int ((6 : ℕ) : ℤ) :: v1 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hmulS main) (((6 : ℕ) : ℤ)) (((bpar n : ℕ) : ℤ)) (v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((ppar n : ℕ) : ℤ)) (by simp only [HvdH.ppar]; push_cast; ring) (SB) (cost4 hW2 hSB20 hKmulS (iszV (h6c) hWs50) (iszV (hbpar) hWs50))
  have P50 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have P51 : vsz (v1) ≤ V := (vszV (hbpar) hVs50)
  have S : vsh 2 (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 2 * V := by
    rw [vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P50) (Nat.add_le_add (P51) (le_refl 0))) (le_of_eq (by ring))
  have H6 : WordR main _ (fun vs => vs = v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v1 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (1) (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 3) (Nat.le_add_left 3 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 2 ≤ 100) hW100)))
  have H7 : WordR main _ (fun vs => vs = v1 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v3 :: v1 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v3) (v1 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hDD) hVs26) hVW)
  have H8 : WordR main _ (fun vs => vs = v3 :: v1 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v4 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hmulS main) (((12 * D * D : ℕ) : ℤ)) (((bpar n : ℕ) : ℤ)) (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((12 * D * D * bpar n : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost4 hW2 hSB20 hKmulS (iszV (hDD) hWs26) (iszV (hbpar) hWs50))
  have H9 : WordR main _ (fun vs => vs = v4 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int (-1 : ℤ) :: v4 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int (-1 : ℤ)) (v4 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszVneg h1 hVs50) hVW)
  have H10 : WordR main _ (fun vs => vs = .int (-1 : ℤ) :: v4 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v5 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) ((-1 : ℤ)) (((12 * D * D * bpar n : ℕ) : ℤ)) (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((12 * D * D * bpar n - 1 : ℕ) : ℤ)) (by rw [Nat.cast_sub (show (1:ℕ) ≤ 12 * D * D * bpar n by omega)]; ring) (SB) (cost6 hW2 hSB20 hKadd hneg1isz (iszV (hDDb) hWs50))
  have H11 : WordR main _ (fun vs => vs = v5 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v6 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hsqrt main) (((12 * D * D * bpar n - 1 : ℕ) : ℤ)) (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (znonneg (12 * D * D * bpar n - 1)) (((Nat.sqrt (12 * D * D * bpar n - 1) : ℕ) : ℤ)) (by rw [Int.toNat_natCast]) (SB) (cost5 hW2 hSB20 hKsqrt (iszV (hDDb1) hWs50))
  have H12 : WordR main _ (fun vs => vs = v6 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v7 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hsqrt main) (((Nat.sqrt (12 * D * D * bpar n - 1) : ℕ) : ℤ)) (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (znonneg (Nat.sqrt (12 * D * D * bpar n - 1))) (((Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1)) : ℕ) : ℤ)) (by rw [Int.toNat_natCast]) (SB) (cost5 hW2 hSB20 hKsqrt (iszV (hSQ1) hWs50))
  have H13 : WordR main _ (fun vs => vs = v7 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((1 : ℕ) : ℤ) :: v7 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int ((1 : ℕ) : ℤ)) (v7 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (h1) hVs50) hVW)
  have H14 : WordR main _ (fun vs => vs = .int ((1 : ℕ) : ℤ) :: v7 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) (((1 : ℕ) : ℤ)) (((Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1)) : ℕ) : ℤ)) (v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((apar n : ℕ) : ℤ)) (by simp only [HvdH.apar]; push_cast; ring) (SB) (cost6 hW2 hSB20 hKadd (iszV (h1) hWs50) (iszV (hSQ2) hWs50))
  have P140 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have P141 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have P142 : vsz (v1) ≤ V := (vszV (hbpar) hVs50)
  have P143 : vsz (.int ((n : ℕ) : ℤ)) ≤ V := (vszV (hNsz) hVs50)
  have S : vsh 4 (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 4 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P140) (Nat.add_le_add (P141) (Nat.add_le_add (P142) (Nat.add_le_add (P143) (le_refl 0))))) (le_of_eq (by ring))
  have H15 : WordR main _ (fun vs => vs = v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((n : ℕ) : ℤ) :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (3) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 4) (Nat.le_add_left 4 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 4 ≤ 100) hW100)))
  have H16 : WordR main _ (fun vs => vs = .int ((n : ℕ) : ℤ) :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((4 : ℕ) : ℤ) :: .int ((n : ℕ) : ℤ) :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int ((4 : ℕ) : ℤ)) (.int ((n : ℕ) : ℤ) :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (h4c) hVs50) hVW)
  have H17 : WordR main _ (fun vs => vs = .int ((4 : ℕ) : ℤ) :: .int ((n : ℕ) : ℤ) :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v9 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hmulS main) (((4 : ℕ) : ℤ)) (((n : ℕ) : ℤ)) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((4 * n : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost4 hW2 hSB20 hKmulS (iszV (h4c) hWs50) (iszV (hNsz) hWs50))
  have P170 : vsz (v9) ≤ V := (vszV (hN4) hVs50)
  have P171 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have P172 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have P173 : vsz (v1) ≤ V := (vszV (hbpar) hVs50)
  have S : vsh 4 (v9 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 4 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P170) (Nat.add_le_add (P171) (Nat.add_le_add (P172) (Nat.add_le_add (P173) (le_refl 0))))) (le_of_eq (by ring))
  have H18 : WordR main _ (fun vs => vs = v9 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v1 :: v9 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (3) (v9 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 5) (Nat.le_add_left 5 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 4 ≤ 100) hW100)))
  have H19 : WordR main _ (fun vs => vs = v1 :: v9 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v10 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) (((bpar n : ℕ) : ℤ)) (((4 * n : ℕ) : ℤ)) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((4 * n + bpar n : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost6 hW2 hSB20 hKadd (iszV (hbpar) hWs50) (iszV (hN4) hWs50))
  have H20 : WordR main _ (fun vs => vs = v10 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int (-1 : ℤ) :: v10 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int (-1 : ℤ)) (v10 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszVneg h1 hVs50) hVW)
  have H21 : WordR main _ (fun vs => vs = .int (-1 : ℤ) :: v10 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v11 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) ((-1 : ℤ)) (((4 * n + bpar n : ℕ) : ℤ)) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((4 * n + bpar n - 1 : ℕ) : ℤ)) (by rw [Nat.cast_sub (show (1:ℕ) ≤ 4 * n + bpar n by omega)]; ring) (SB) (cost6 hW2 hSB20 hKadd hneg1isz (iszV (hN4b) hWs50))
  have P210 : vsz (v11) ≤ V := (vszV (hN4b1) hVs50)
  have P211 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have P212 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have P213 : vsz (v1) ≤ V := (vszV (hbpar) hVs50)
  have S : vsh 4 (v11 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 4 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P210) (Nat.add_le_add (P211) (Nat.add_le_add (P212) (Nat.add_le_add (P213) (le_refl 0))))) (le_of_eq (by ring))
  have H22 : WordR main _ (fun vs => vs = v11 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v1 :: v11 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (3) (v11 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 5) (Nat.le_add_left 5 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 4 ≤ 100) hW100)))
  have H23 : WordR main _ (fun vs => vs = v1 :: v11 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v11 :: v1 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    swapStep hK (hswap main) (v1) (v11) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost2 hW2 hSB20 hKswap (vszV (hbpar) hVs50) (vszV (hN4b1) hVs50) hVW)
  have H24 : WordR main _ (fun vs => vs = v11 :: v1 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v12 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hfdiv main) (((4 * n + bpar n - 1 : ℕ) : ℤ)) (((bpar n : ℕ) : ℤ)) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Hbparpos) ((((4 * n + bpar n - 1) / bpar n : ℕ) : ℤ)) (by rw [Int.ofNat_fdiv]) (SB) (cost4 hW2 hSB20 hKfdiv (iszV (hN4b1) hWs50) (iszV (hbpar) hWs50))
  have H25 : WordR main _ (fun vs => vs = v12 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hclog2 main) ((((4 * n + bpar n - 1) / bpar n : ℕ) : ℤ)) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (znonneg ((4 * n + bpar n - 1) / bpar n)) (((kTpar n : ℕ) : ℤ)) (by rw [Int.toNat_natCast, HvdH.kTpar]) (SB) (cost9 hW2 hSB20 hKclog2 (iszV (hQV) hWs50))
  have H26 : WordR main _ (fun vs => vs = v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v13 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    dupStep hK (hdup main) (v13) (v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKdup (vszV (hkTpar) hVs50) hVW)
  have H27 : WordR main _ (fun vs => vs = v13 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hpow2 main) (((kTpar n : ℕ) : ℤ)) (v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (znonneg (kTpar n)) (((Tpar n : ℕ) : ℤ)) (by rw [Int.toNat_natCast, HvdH.Tpar]; push_cast; rfl) (SB) (cost6 hW2 hSB20 hKpow2 (by omega) (iszV (hkTpar) hWs50))
  have P270 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P271 : vsz (v13) ≤ V := (vszV (hkTpar) hVs50)
  have S : vsh 2 (v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 2 * V := by
    rw [vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P270) (Nat.add_le_add (P271) (le_refl 0))) (le_of_eq (by ring))
  have H28 : WordR main _ (fun vs => vs = v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v13 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (1) (v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 6) (Nat.le_add_left 6 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 2 ≤ 100) hW100)))
  have H29 : WordR main _ (fun vs => vs = v13 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v15 :: v13 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v15) (v13 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hDm1) hVs50) hVW)
  have H30 : WordR main _ (fun vs => vs = v15 :: v13 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v16 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) (((D - 1 : ℕ) : ℤ)) (((kTpar n : ℕ) : ℤ)) (v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((kTpar n + (D - 1) : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost6 hW2 hSB20 hKadd (iszV (hDm1) hWs50) (iszV (hkTpar) hWs50))
  have H31 : WordR main _ (fun vs => vs = v16 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((D : ℕ) : ℤ) :: v16 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int ((D : ℕ) : ℤ)) (v16 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hD) hVs50) hVW)
  have H32 : WordR main _ (fun vs => vs = .int ((D : ℕ) : ℤ) :: v16 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v16 :: .int ((D : ℕ) : ℤ) :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    swapStep hK (hswap main) (.int ((D : ℕ) : ℤ)) (v16) (v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost2 hW2 hSB20 hKswap (vszV (hD) hVs50) (vszV ((szAdd_le2 hkTpar hDm1)) hVs51) hVW)
  have H33 : WordR main _ (fun vs => vs = v16 :: .int ((D : ℕ) : ℤ) :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hfdiv main) (((kTpar n + (D - 1) : ℕ) : ℤ)) (((D : ℕ) : ℤ)) (v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Hdpos) (((krpar n : ℕ) : ℤ)) (by rw [show krpar n = (kTpar n + (D - 1)) / D from krpar_eq n, Int.ofNat_fdiv]) (SB) (cost4 hW2 hSB20 hKfdiv (iszV ((szAdd_le2 hkTpar hDm1)) hWs51) (iszV (hD) hWs50))
  have H34 : WordR main _ (fun vs => vs = v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v17 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    dupStep hK (hdup main) (v17) (v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKdup (vszV (hkrpar) hVs50) hVW)
  have H35 : WordR main _ (fun vs => vs = v17 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hpow2 main) (((krpar n : ℕ) : ℤ)) (v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (znonneg (krpar n)) (((rpar n : ℕ) : ℤ)) (by rw [Int.toNat_natCast, HvdH.rpar]; push_cast; rfl) (SB) (cost6 hW2 hSB20 hKpow2 (by omega) (iszV (hkrpar) hWs50))
  have P350 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P351 : vsz (v17) ≤ V := (vszV (hkrpar) hVs50)
  have S : vsh 2 (v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 2 * V := by
    rw [vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P350) (Nat.add_le_add (P351) (le_refl 0))) (le_of_eq (by ring))
  have H36 : WordR main _ (fun vs => vs = v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v17 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (1) (v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 8) (Nat.le_add_left 8 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 2 ≤ 100) hW100)))
  have H37 : WordR main _ (fun vs => vs = v17 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((D : ℕ) : ℤ) :: v17 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int ((D : ℕ) : ℤ)) (v17 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hD) hVs50) hVW)
  have H38 : WordR main _ (fun vs => vs = .int ((D : ℕ) : ℤ) :: v17 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hmulS main) (((D : ℕ) : ℤ)) (((krpar n : ℕ) : ℤ)) (v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((D * krpar n : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost4 hW2 hSB20 hKmulS (iszV (hD) hWs50) (iszV (hkrpar) hWs50))
  have P380 : vsz (v19) ≤ V := (vszV (hDKR) hVs50)
  have P381 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P382 : vsz (v17) ≤ V := (vszV (hkrpar) hVs50)
  have P383 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P384 : vsz (v13) ≤ V := (vszV (hkTpar) hVs50)
  have S : vsh 5 (v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 5 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P380) (Nat.add_le_add (P381) (Nat.add_le_add (P382) (Nat.add_le_add (P383) (Nat.add_le_add (P384) (le_refl 0)))))) (le_of_eq (by ring))
  have H39 : WordR main _ (fun vs => vs = v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v13 :: v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (4) (v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 4 < 9) (Nat.le_add_left 9 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 5 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 5 ≤ 100) hW100)))
  have H40 : WordR main _ (fun vs => vs = v13 :: v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int (-(kTpar n : ℤ)) :: v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    unStepP hK (hneg main) (((kTpar n : ℕ) : ℤ)) (v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (by trivial) ((-(kTpar n : ℤ))) rfl (SB) (cost9 hW2 hSB20 hKneg (iszV (hkTpar) hWs50))
  have H41 : WordR main _ (fun vs => vs = .int (-(kTpar n : ℤ)) :: v19 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v20 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) ((-((kTpar n : ℕ) : ℤ))) (((D * krpar n : ℕ) : ℤ)) (v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ((by trivial)) (((dpar n : ℕ) : ℤ)) (by rw [show dpar n = D * krpar n - kTpar n from rfl, Nat.cast_sub (kT_le_Dkr n)]; ring) (SB) (cost6 hW2 hSB20 hKadd (iszVneg (hkTpar) hWs50) (iszV (hDKR) hWs50))
  have P410 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
  have P411 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P412 : vsz (v17) ≤ V := (vszV (hkrpar) hVs50)
  have S : vsh 3 (v20 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 3 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P410) (Nat.add_le_add (P411) (Nat.add_le_add (P412) (le_refl 0)))) (le_of_eq (by ring))
  have H42 : WordR main _ (fun vs => vs = v20 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v17 :: v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (2) (v20 :: v18 :: v17 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 2 < 9) (Nat.le_add_left 9 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 3 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 3 ≤ 100) hW100)))
  have H43 : WordR main _ (fun vs => vs = v17 :: v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    dropStep hK (hdrop main) (v17) (v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKdrop (vszV (hkrpar) hVs50) hVW)
  have P430 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
  have P431 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P432 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P433 : vsz (v13) ≤ V := (vszV (hkTpar) hVs50)
  have S : vsh 4 (v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 4 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P430) (Nat.add_le_add (P431) (Nat.add_le_add (P432) (Nat.add_le_add (P433) (le_refl 0))))) (le_of_eq (by ring))
  have H44 : WordR main _ (fun vs => vs = v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v13 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (3) (v20 :: v18 :: v14 :: v13 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 8) (Nat.le_add_left 8 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 4 ≤ 100) hW100)))
  have H45 : WordR main _ (fun vs => vs = v13 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ => (SB)) :=
    dropStep hK (hdrop main) (v13) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (SB) (cost1 hW2 hSB20 hKdrop (vszV (hkTpar) hVs50) hVW)
  have P450 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
  have P451 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P452 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P453 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have P454 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have P455 : vsz (v1) ≤ V := (vszV (hbpar) hVs50)
  have P456 : vsz (.int ((n : ℕ) : ℤ)) ≤ V := (vszV (hNsz) hVs50)
  have S : vsh 7 (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) ≤ 7 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P450) (Nat.add_le_add (P451) (Nat.add_le_add (P452) (Nat.add_le_add (P453) (Nat.add_le_add (P454) (Nat.add_le_add (P455) (Nat.add_le_add (P456) (le_refl 0)))))))) (le_of_eq (by ring))
  have H46 : WordR main _ (fun vs => vs = v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((n : ℕ) : ℤ) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (6) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: .int ((n : ℕ) : ℤ) :: R) (Nat.lt_of_lt_of_le (by norm_num : 6 < 7) (Nat.le_add_left 7 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 7 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 7 ≤ 100) hW100)))
  have H47 : WordR main _ (fun vs => vs = .int ((n : ℕ) : ℤ) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    dropStep hK (hdrop main) (.int ((n : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKdrop (vszV (hNsz) hVs50) hVW)
  have P470 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
  have P471 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have S : vsh 2 (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 2 * V := by
    rw [vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P470) (Nat.add_le_add (P471) (le_refl 0))) (le_of_eq (by ring))
  have H48 : WordR main _ (fun vs => vs = v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pickStep hK (hpick main) (1) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 6) (Nat.le_add_left 6 R.length)) (SB) (cost3 hW2 hSB20 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 2 ≤ 100) hW100)))
  have H49 : WordR main _ (fun vs => vs = v18 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v21 :: v18 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v21) (v18 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (h2Dm1) hVs50) hVW)
  have H50 : WordR main _ (fun vs => vs = v21 :: v18 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v22 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hmulS main) ((((2 * D - 1) : ℕ) : ℤ)) (((rpar n : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((rpar n * (2 * D - 1) : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost4 hW2 hSB20 hKmulS (iszV (h2Dm1) hWs50) (iszV (hrpar) hWs50))
  have H51 : WordR main _ (fun vs => vs = v22 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v23 :: v22 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v23) (v22 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (h4D) hVs50) hVW)
  have H52 : WordR main _ (fun vs => vs = v23 :: v22 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v22 :: v23 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    swapStep hK (hswap main) (v23) (v22) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost2 hW2 hSB20 hKswap (vszV (h4D) hVs50) (vszV (hR2D1) hVs50) hVW)
  have H53 : WordR main _ (fun vs => vs = v22 :: v23 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v24 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hfdiv main) (((rpar n * (2 * D - 1) : ℕ) : ℤ)) ((((4 * D) : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (H4Dpos) (((rpar n * (2 * D - 1) / (4 * D) : ℕ) : ℤ)) (by rw [Int.ofNat_fdiv]) (SB) (cost4 hW2 hSB20 hKfdiv (iszV (hR2D1) hWs50) (iszV (h4D) hWs50))
  have H54 : WordR main _ (fun vs => vs = v24 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((1 : ℕ) : ℤ) :: v24 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (.int ((1 : ℕ) : ℤ)) (v24 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (h1) hVs50) hVW)
  have H55 : WordR main _ (fun vs => vs = .int ((1 : ℕ) : ℤ) :: v24 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v25 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) (((1 : ℕ) : ℤ)) (((rpar n * (2 * D - 1) / (4 * D) : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((Lpar n : ℕ) : ℤ)) (by simp only [Work.Params.Lpar]; push_cast; ring) (SB) (cost6 hW2 hSB20 hKadd (iszV (h1) hWs50) (iszV (hR4D) hWs50))
  have H56 : WordR main _ (fun vs => vs = v25 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v26 :: v25 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v26) (v25 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hK1) hVs50) hVW)
  have H57 : WordR main _ (fun vs => vs = v26 :: v25 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v27 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) (((Ffac * Qall - 1 - Qall : ℕ) : ℤ)) (((Lpar n : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((Lpar n + Ffac * Qall - 1 - Qall : ℕ) : ℤ)) (by
        have hL1 : (1:ℕ) ≤ Lpar n := Nat.succ_le_of_lt hLpos
        have h1 : (1:ℕ) ≤ Lpar n + Ffac * Qall :=
          le_trans hL1 (Nat.le_add_right (Lpar n) (Ffac * Qall))
        have hQ1 : (1:ℕ) ≤ Qall :=
          Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Qall_pos)
        have hQlt : Qall < Ffac * Qall := by
          have h2Q : 2 * Qall ≤ Ffac * Qall := Nat.mul_le_mul_right Qall Ffac_two_le
          omega
        have h1' : (1:ℕ) ≤ Ffac * Qall := Nat.mul_pos Ffac_pos Qall_pos
        have h2 : Qall ≤ (Lpar n + Ffac * Qall) - 1 :=
          Nat.le_sub_one_of_lt (lt_of_lt_of_le hQlt (Nat.le_add_left (Ffac * Qall) (Lpar n)))
        have h2' : Qall ≤ Ffac * Qall - 1 := Nat.le_sub_one_of_lt hQlt
        rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_add (Lpar n) (Ffac * Qall),
            Nat.cast_sub h2', Nat.cast_sub h1']
        ring) (SB) (cost6 hW2 hSB20 hKadd (iszV (hK1) hWs50) (iszV (hLpar) hWs50))
  have H58 : WordR main _ (fun vs => vs = v27 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v28 :: v27 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v28) (v27 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hFQ) hVs50) hVW)
  have H59 : WordR main _ (fun vs => vs = v28 :: v27 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v27 :: v28 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    swapStep hK (hswap main) (v28) (v27) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost2 hW2 hSB20 hKswap (vszV (hFQ) hVs50) (vszV (hLK1) hVs50) hVW)
  have H60 : WordR main _ (fun vs => vs = v27 :: v28 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v29 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hfdiv main) (((Lpar n + Ffac * Qall - 1 - Qall : ℕ) : ℤ)) (((Ffac * Qall : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (HFQpos) ((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall) : ℕ) : ℤ)) (by rw [Int.ofNat_fdiv]) (SB) (cost4 hW2 hSB20 hKfdiv (iszV (hLK1) hWs50) (iszV (hFQ) hWs50))
  have H61 : WordR main _ (fun vs => vs = v29 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v28 :: v29 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v28) (v29 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hFQ) hVs50) hVW)
  have H62 : WordR main _ (fun vs => vs = v28 :: v29 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v30 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hmulS main) (((Ffac * Qall : ℕ) : ℤ)) ((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall) : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall) : ℕ) : ℤ)) (by push_cast; ring) (SB) (cost4 hW2 hSB20 hKmulS (iszV (hFQ) hWs50) (iszV (hMM) hWs50))
  have H63 : WordR main _ (fun vs => vs = v30 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v31 :: v30 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (v31) (v30 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush (vszV (hQall) hVs50) hVW)
  have H64 : WordR main _ (fun vs => vs = v31 :: v30 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    binStepP hK (hadd main) (((Qall : ℕ) : ℤ)) (((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall) : ℕ) : ℤ)) (v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((upar n : ℕ) : ℤ)) (by simp only [Work.Params.upar]; push_cast; ring) (SB) (cost6 hW2 hSB20 hKadd (iszV (hQall) hWs50) (iszV (hMFQ) hWs50))
  have CHAIN := seqC hK (seqC hK (seqC hK (seqC hK (seqC hK (seqC hK (H1) (H2)) (seqC hK (H3) (H4))) (seqC hK (seqC hK (H5) (H6)) (seqC hK (H7) (H8)))) (seqC hK (seqC hK (seqC hK (H9) (H10)) (seqC hK (H11) (H12))) (seqC hK (seqC hK (H13) (H14)) (seqC hK (H15) (H16))))) (seqC hK (seqC hK (seqC hK (seqC hK (H17) (H18)) (seqC hK (H19) (H20))) (seqC hK (seqC hK (H21) (H22)) (seqC hK (H23) (H24)))) (seqC hK (seqC hK (seqC hK (H25) (H26)) (seqC hK (H27) (H28))) (seqC hK (seqC hK (H29) (H30)) (seqC hK (H31) (H32)))))) (seqC hK (seqC hK (seqC hK (seqC hK (seqC hK (H33) (H34)) (seqC hK (H35) (H36))) (seqC hK (seqC hK (H37) (H38)) (seqC hK (H39) (H40)))) (seqC hK (seqC hK (seqC hK (H41) (H42)) (seqC hK (H43) (H44))) (seqC hK (seqC hK (H45) (H46)) (seqC hK (H47) (H48))))) (seqC hK (seqC hK (seqC hK (seqC hK (H49) (H50)) (seqC hK (H51) (H52))) (seqC hK (seqC hK (H53) (H54)) (seqC hK (H55) (H56)))) (seqC hK (seqC hK (seqC hK (H57) (H58)) (seqC hK (H59) (H60))) (seqC hK (seqC hK (H61) (H62)) (seqC hK (H63) (H64))))))
  exact conseqC hK CHAIN ((Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 8 8 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 8 8 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 16 16 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 8 8 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 4 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 8 8 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 16 16 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 32 32 SB)))))

theorem seg2
    (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (main : Cmd) (n : ℕ) (R : List Val)
    (dupP : Cmd)
    (Kdup : ℕ)
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest) (fun vs => Kdup * (vsz (vs.headD .nil) + 1)))
    (dropP : Cmd)
    (Kdrop : ℕ)
    (hdrop : ∀ main : Cmd, WordR main dropP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest) (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (swapP : Cmd)
    (Kswap : ℕ)
    (hswap : ∀ main : Cmd, WordR main swapP (fun vs => 2 ≤ vs.length) (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest) (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (pickP : ℕ → Cmd)
    (Kpick : ℕ)
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs) (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (rollP : ℕ → Cmd)
    (Kroll : ℕ)
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k) (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (pushP : Val → Cmd)
    (Kpush : ℕ)
    (hpush : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs) (fun _ => Kpush * (vsz v + 1)))
    (ifZeroP : Cmd → Cmd → Cmd)
    (KifZero : ℕ)
    (hifZero : ∀ (main q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ), (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) → (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) → WordR main (ifZeroP q₁ q₂) (fun vs => vs = .int z :: rest) (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => KifZero * (isz z + 1) + max c₁ c₂))
    (mapListP : Cmd → Cmd)
    (KmapList : ℕ)
    (hmapList : ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ), (∀ x : Val, P x → WordR main q (fun vs => vs = x :: rest) (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) → ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) → WordR main (mapListP q) (fun vs => vs = ofList xs :: rest) (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys) (fun _ => xs.length * (c + KmapList * (L + 1)) + KmapList))
    (addP : Cmd)
    (Kadd : ℕ)
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (fun a b => a + b) (fun a b => Kadd * (isz a + isz b)))
    (subP : Cmd)
    (Ksub : ℕ)
    (hsub : ∀ main : Cmd, BinOp main subP (fun _ _ => True) (fun a b => a - b) (fun a b => Ksub * (isz a + isz b)))
    (negP : Cmd)
    (Kneg : ℕ)
    (hneg : ∀ main : Cmd, UnOp main negP (fun _ => True) (fun a => -a) (fun a => Kneg * isz a))
    (ltP : Cmd)
    (Klt : ℕ)
    (hlt : ∀ main : Cmd, BinOp main ltP (fun _ _ => True) (fun a b => if a < b then 1 else 0) (fun a b => Klt * (isz a + isz b)))
    (mulSP : Cmd)
    (KmulS : ℕ)
    (hmulS : ∀ main : Cmd, BinOp main mulSP (fun _ _ => True) (fun a b => a * b) (fun a b => KmulS * isz a * isz b))
    (fdivP : Cmd)
    (Kfdiv : ℕ)
    (hfdiv : ∀ main : Cmd, BinOp main fdivP (fun a b => 0 < b) Int.fdiv (fun a b => Kfdiv * isz a * isz b))
    (sqrtP : Cmd)
    (Ksqrt : ℕ)
    (hsqrt : ∀ main : Cmd, UnOp main sqrtP (fun a => 0 ≤ a) (fun a => ↑a.toNat.sqrt) (fun a => Ksqrt * isz a ^ 2))
    (clog2P : Cmd)
    (Kclog2 : ℕ)
    (hclog2 : ∀ main : Cmd, UnOp main clog2P (fun a => 0 ≤ a) (fun a => ↑(Nat.clog 2 a.toNat)) (fun a => Kclog2 * isz a))
    (pow2P : Cmd)
    (Kpow2 : ℕ)
    (hpow2 : ∀ main : Cmd, UnOp main pow2P (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat) (fun k => Kpow2 * (k.toNat + isz k)))
    (Ksum K0 B W V SB : ℕ)
    (hKsumdef : Ksum = Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + KifZero + KmapList + Kadd + Ksub + Kneg + Klt + KmulS + Kfdiv + Ksqrt + Kclog2 + Kpow2)
    (hK0def : K0 = Ksum + 2 ^ 44 + 100)
    (hBdef : B = n.size + 1)
    (hVdef : V = (KBsz + n.size + 6) * (D + 2))
    (hWdef : W = B ^ K0)
    (hSBdef : SB = W ^ 40)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hsz : 65755586 ≤ n.size)
    (hn2 : 1 < n)
    (hK0pos : 1 ≤ K0)
    (hK0ge : 2 ^ 44 + 100 ≤ K0)
    (hB2 : 2 ≤ B)
    (hVdef2 : V = (KBsz + n.size + 6) * (D + 2))
    (hW2 : 2 ≤ W)
    (hW4 : 4 ≤ W)
    (hW100 : 100 ≤ W)
    (hVW : V + 1 ≤ W)
    (hVsz : n.size + 100 ≤ V)
    (hK0W : K0 ≤ W)
    (hKdupW : Kdup ≤ W)
    (hKdropW : Kdrop ≤ W)
    (hKswapW : Kswap ≤ W)
    (hKpickW : Kpick ≤ W)
    (hKrollW : Kroll ≤ W)
    (hKpushW : Kpush ≤ W)
    (hKifZeroW : KifZero ≤ W)
    (hKmapListW : KmapList ≤ W)
    (hKaddW : Kadd ≤ W)
    (hKsubW : Ksub ≤ W)
    (hKnegW : Kneg ≤ W)
    (hKltW : Klt ≤ W)
    (hKmulSW : KmulS ≤ W)
    (hKfdivW : Kfdiv ≤ W)
    (hKsqrtW : Ksqrt ≤ W)
    (hKclog2W : Kclog2 ≤ W)
    (hKpow2W : Kpow2 ≤ W)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hW77 : 77 ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hSB20 : W ^ 20 ≤ SB)
    (hSB30 : W ^ 20 ≤ W ^ 30)
    (hSB34 : W ^ 34 ≤ W ^ 34)
    (hSB37 : W ^ 37 ≤ SB)
    (hbparT : (bpar n).size ≤ n.size + 4)
    (hpparT : (ppar n).size ≤ n.size + 4)
    (haparT : (apar n).size ≤ n.size + 4)
    (hkTparT : (kTpar n).size ≤ n.size + 4)
    (hTparT : (Tpar n).size ≤ n.size + 4)
    (hkrparT : (krpar n).size ≤ n.size + 4)
    (hrparT : (rpar n).size ≤ n.size + 4)
    (hdparT : (dpar n).size ≤ n.size + 4)
    (hLparT : (Lpar n).size ≤ n.size + 4)
    (huparT : (upar n).size ≤ n.size + 4)
    (hNsz : n.size ≤ n.size + 50)
    (hbpar : (bpar n).size ≤ n.size + 50)
    (hppar : (ppar n).size ≤ n.size + 50)
    (hapar : (apar n).size ≤ n.size + 50)
    (hkTpar : (kTpar n).size ≤ n.size + 50)
    (hTpar : (Tpar n).size ≤ n.size + 50)
    (hkrpar : (krpar n).size ≤ n.size + 50)
    (hrpar : (rpar n).size ≤ n.size + 50)
    (hdpar : (dpar n).size ≤ n.size + 50)
    (hLpar : (Lpar n).size ≤ n.size + 50)
    (hupar : (upar n).size ≤ n.size + 50)
    (hupar4 : (upar n).size ≤ n.size + 4)
    (h6c : (6:ℕ).size ≤ n.size + 50)
    (h1 : (1:ℕ).size ≤ n.size + 50)
    (h2c : (2:ℕ).size ≤ n.size + 50)
    (h4c : (4:ℕ).size ≤ n.size + 50)
    (hD : (D:ℕ).size ≤ n.size + 50)
    (hDv : (D:ℕ).size ≤ 11)
    (hDm1 : (D - 1).size ≤ n.size + 50)
    (h2Dm1v : (2 * D - 1).size ≤ 13)
    (h2Dm1 : (2 * D - 1).size ≤ n.size + 50)
    (h4Dv : (4 * D).size ≤ 14)
    (h4D : (4 * D).size ≤ n.size + 50)
    (hFfacT : (Ffac).size ≤ n.size + 4)
    (hQallT : (Qall).size ≤ n.size + 4)
    (hFfac : (Ffac).size ≤ n.size + 50)
    (hFfac4 : (Ffac).size ≤ n.size + 4)
    (hQall : (Qall).size ≤ n.size + 50)
    (hFQ3 : (Ffac * Qall).size ≤ n.size + 4)
    (hFQ : (Ffac * Qall).size ≤ n.size + 50)
    (hK13 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hK1 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (h2Fv : (2 * Ffac).size ≤ n.size + 4)
    (h2F : (2 * Ffac).size ≤ n.size + 50)
    (h2F4 : (2 * Ffac).size ≤ n.size + 4)
    (hDD : (12 * D * D).size ≤ 26)
    (hDDbT : (12 * D * D * bpar n).size ≤ n.size + 30)
    (hDDb : (12 * D * D * bpar n).size ≤ n.size + 50)
    (hDDb1 : (12 * D * D * bpar n - 1).size ≤ n.size + 50)
    (hSQ1 : (Nat.sqrt (12 * D * D * bpar n - 1)).size ≤ n.size + 50)
    (hSQ2 : (Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1))).size ≤ n.size + 50)
    (hN4T : (4 * n).size ≤ n.size + 3)
    (hN4 : (4 * n).size ≤ n.size + 50)
    (hN4bT : (4 * n + bpar n).size ≤ n.size + 5)
    (hN4b : (4 * n + bpar n).size ≤ n.size + 50)
    (hN4b1 : (4 * n + bpar n - 1).size ≤ n.size + 50)
    (hQVT : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 5)
    (hQV : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 50)
    (hDKRT : (D * krpar n).size ≤ n.size + 20)
    (hDKR : (D * krpar n).size ≤ n.size + 50)
    (hR2D1T : (rpar n * (2 * D - 1)).size ≤ n.size + 20)
    (hR2D1 : (rpar n * (2 * D - 1)).size ≤ n.size + 50)
    (hR4D : (rpar n * (2 * D - 1) / (4 * D)).size ≤ n.size + 50)
    (hLK1T : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 5)
    (hLK1 : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (hMMT : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 5)
    (hMM : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 50)
    (hMFQ : (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall)).size ≤ n.size + 50)
    (hVLD : vsz (HvdH.intList (List.range D)) ≤ V)
    (hVss : vsz (HvdH.intList (ssPar n)) ≤ V)
    (hVts : vsz (HvdH.intList (tsPar n)) ≤ V)
    (hVLD2 : vsz (intList2 (List.range D)) ≤ V)
    (hVssl : vsz (intList2 (ssPar n)) ≤ V)
    (hVtsl : vsz (intList2 (tsPar n)) ≤ V)
    (hDleW : D ≤ W)
    (hbparposN : 0 < bpar n)
    (hkTw : kTpar n ≤ W)
    (hkrw : krpar n ≤ W)
    (hLpos : 0 < Lpar n)
    (huparpos : 0 < upar n)
    (hposDDb : 0 < 12 * D * D * bpar n)
    (hposN4b : 0 < 4 * n + bpar n)
    (hneg1isz : isz (-1 : ℤ) ≤ W)
    (Hbparpos : (0:ℤ) < (bpar n : ℤ))
    (Hdpos : (0:ℤ) < (D : ℤ))
    (H4Dpos : (0:ℤ) < (4 * D : ℤ))
    (HFQpos : (0:ℤ) < (Ffac * Qall : ℤ))
    (hDle : HvdH.D ≤ 2 ^ 11)
    (hVs26 : (26:ℕ) + 2 ≤ V)
    (hVs51 : n.size + 50 + 1 + 2 ≤ V)
    (hVs11 : (11:ℕ) + 2 ≤ V)
    (hVs12 : (12:ℕ) + 2 ≤ V)
    (hVs24 : ((n.size + 4) + 2) + 2 ≤ V)
    (hVsFk : ((n.size + 4) + 12) + 2 ≤ V)
    (hVsUk : (((n.size + 4) + 12) + 1) + 2 ≤ V)
    (hVs50 : n.size + 50 + 2 ≤ V)
    (hVWle : V ≤ W)
    (hWs26 : (26:ℕ) + 2 ≤ W)
    (hWs51 : n.size + 50 + 1 + 2 ≤ W)
    (hWs11 : (11:ℕ) + 2 ≤ W)
    (hWs12 : (12:ℕ) + 2 ≤ W)
    (hWs24 : ((n.size + 4) + 2) + 2 ≤ W)
    (hWsFk : ((n.size + 4) + 12) + 2 ≤ W)
    (hWsUk : (((n.size + 4) + 12) + 1) + 2 ≤ W)
    (hWs50 : n.size + 50 + 2 ≤ W)
    (hc6 : Nat.size 6 ≤ n.size + 4)
    (hcDD : (12 * D * D).size ≤ n.size + 4)
    (hc1 : Nat.size 1 ≤ n.size + 4)
    (hc4 : Nat.size 4 ≤ n.size + 4)
    (hcDm1 : (D - 1).size ≤ n.size + 4)
    (hcDz : D.size ≤ n.size + 4)
    (hc2Dm1 : (2 * D - 1).size ≤ n.size + 4)
    (hc4D : (4 * D).size ≤ n.size + 4)
    (hcF : Ffac.size ≤ n.size + 4)
    (hcQ : Qall.size ≤ n.size + 4)
    (hcFQ : (Ffac * Qall).size ≤ n.size + 4)
    (hcK1z : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hc2F : (2 * Ffac).size ≤ n.size + 4)
    :
    WordR main (Cmd.seq ((pushP (intList2 (List.range D)))) ((mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP)))))))))))) (fun vs => vs = .int ((upar n : ℕ) : ℤ) :: .int ((dpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((bpar n : ℕ) : ℤ) :: R) (fun _ out => out = intList2 (ssPar n) :: .int ((upar n : ℕ) : ℤ) :: .int ((dpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((bpar n : ℕ) : ℤ) :: R) (fun _ => 2 * SB) := by
  let v1 : Val := .int ((bpar n : ℕ) : ℤ)
  let v2 : Val := .int ((ppar n : ℕ) : ℤ)
  let v3 : Val := .int ((12 * D * D : ℕ) : ℤ)
  let v4 : Val := .int ((12 * D * D * bpar n : ℕ) : ℤ)
  let v5 : Val := .int ((12 * D * D * bpar n - 1 : ℕ) : ℤ)
  let v6 : Val := .int ((Nat.sqrt (12 * D * D * bpar n - 1) : ℕ) : ℤ)
  let v7 : Val := .int ((Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1)) : ℕ) : ℤ)
  let v8 : Val := .int ((apar n : ℕ) : ℤ)
  let v9 : Val := .int ((4 * n : ℕ) : ℤ)
  let v10 : Val := .int ((4 * n + bpar n : ℕ) : ℤ)
  let v11 : Val := .int ((4 * n + bpar n - 1 : ℕ) : ℤ)
  let v12 : Val := .int (((4 * n + bpar n - 1) / bpar n : ℕ) : ℤ)
  let v13 : Val := .int ((kTpar n : ℕ) : ℤ)
  let v14 : Val := .int ((Tpar n : ℕ) : ℤ)
  let v15 : Val := .int ((D - 1 : ℕ) : ℤ)
  let v16 : Val := .int ((kTpar n + (D - 1) : ℕ) : ℤ)
  let v17 : Val := .int ((krpar n : ℕ) : ℤ)
  let v18 : Val := .int ((rpar n : ℕ) : ℤ)
  let v19 : Val := .int ((D * krpar n : ℕ) : ℤ)
  let v20 : Val := .int ((dpar n : ℕ) : ℤ)
  let v21 : Val := .int (((2 * D - 1) : ℕ) : ℤ)
  let v22 : Val := .int ((rpar n * (2 * D - 1) : ℕ) : ℤ)
  let v23 : Val := .int (((4 * D) : ℕ) : ℤ)
  let v24 : Val := .int ((rpar n * (2 * D - 1) / (4 * D) : ℕ) : ℤ)
  let v25 : Val := .int ((Lpar n : ℕ) : ℤ)
  let v26 : Val := .int ((Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v27 : Val := .int ((Lpar n + Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v28 : Val := .int ((Ffac * Qall : ℕ) : ℤ)
  let v29 : Val := .int (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall) : ℕ) : ℤ)
  let v30 : Val := .int ((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall) : ℕ) : ℤ)
  let v31 : Val := .int ((Qall : ℕ) : ℤ)
  let v32 : Val := .int ((upar n : ℕ) : ℤ)
  have H65 : WordR main _ (fun vs => vs = v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (List.range D) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (intList2 (List.range D)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush hVLD2 hVW)
  have H66 : WordR main (mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP)))))))))) (fun vs => vs = intList2 (List.range D) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => SB) := by
    have hbody : ∀ x : Val, (∃ k : ℕ, k < D ∧ x = Val.int (k:ℤ)) →
        WordR main (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP))))))))) (fun vs => vs = x :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
          (fun _ out => ∃ y, out = y :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R ∧
            (∃ k' : ℕ, x = Val.int (k':ℤ) ∧ y = Val.int ((ssPar n).getD k' 0 : ℤ)) ∧ vsz y ≤ V)
          (fun _ => W ^ 35) := by
      intro x hx
      obtain ⟨k, hkD, rfl⟩ := hx
      let u1 : Val := .int ((k - dpar n : ℕ) : ℤ)
      let u2 : Val := .int ((k - dpar n + 1 : ℕ) : ℤ)
      let u3 : Val := .int ((2 * Ffac : ℕ) : ℤ)
      let u4 : Val := .int ((2 * Ffac * (k - dpar n + 1) : ℕ) : ℤ)
      let u5 : Val := .int ((2 * upar n : ℕ) : ℤ)
      let u6 : Val := .int ((2 * upar n - 1 : ℕ) : ℤ)
      let u7 : Val := .int ((2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1) : ℕ) : ℤ)
      let u8 : Val := .int ((k + 1 : ℕ) : ℤ)
      let u9 : Val := .int ((Ffac : ℕ) : ℤ)
      let u10 : Val := .int ((Ffac * (k + 1) : ℕ) : ℤ)
      let u11 : Val := .int ((upar n + Ffac * (k + 1) : ℕ) : ℤ)
      have hk11 : k.size ≤ 11 := Nat.size_le.mpr (lt_of_lt_of_le hkD hDle)
      have h2sz : (2:ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
      have hk1 : (k + 1).size ≤ 12 := le_trans (size_succ_le k) (le_trans (Nat.add_le_add_right hk11 1) (by norm_num))
      have hFk : (Ffac * (k + 1)).size ≤ (n.size + 4) + 12 := le_trans (size_mul_le Ffac (k + 1)) (Nat.add_le_add hFfac4 hk1)
      have huk : (upar n + Ffac * (k + 1)).size ≤ ((n.size + 4) + 12) + 1 := le_trans (szAdd_le (upar n) (Ffac * (k + 1))) (Nat.add_le_add_right (max_le (le_trans hupar4 (Nat.le_add_right (n.size + 4) 12)) hFk) 1)
      have hkdp : (k - dpar n).size ≤ 11 := le_trans (szSub_le k (dpar n)) hk11
      have hkdp1 : (k - dpar n + 1).size ≤ 12 := le_trans (size_succ_le (k - dpar n)) (le_trans (Nat.add_le_add_right hkdp 1) (by norm_num))
      have h2Fk : (2 * Ffac * (k - dpar n + 1)).size ≤ (n.size + 4) + 12 := le_trans (size_mul_le (2 * Ffac) (k - dpar n + 1)) (Nat.add_le_add h2F4 hkdp1)
      have h2u : (2 * upar n).size ≤ (n.size + 4) + 2 := le_trans (size_mul_le 2 (upar n)) (le_trans (Nat.add_le_add h2sz hupar4) (le_of_eq (Nat.add_comm 2 (n.size + 4))))
      have h2u1 : (2 * upar n - 1).size ≤ (n.size + 4) + 2 := le_trans (szSub_le (2 * upar n) 1) h2u
      have hres1 : (2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1)).size ≤ ((n.size + 4) + 12) + 1 := le_trans (szAdd_le (2 * upar n - 1) (2 * Ffac * (k - dpar n + 1))) (Nat.add_le_add_right (max_le (le_trans h2u1 (Nat.add_le_add_left (by norm_num) (n.size + 4))) h2Fk) 1)
      have c2H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((1 : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pushValStep hK (hpush main) (.int ((1 : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h1) hVs50) hVW)
      have c2H2 : WordR main _ (fun vs => vs = .int ((1 : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        binStepP hK (hadd main) (((1 : ℕ) : ℤ)) (((k : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((k + 1 : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd (iszV (h1) hWs50) (iszV (hk11) hWs11))
      have c2H3 : WordR main _ (fun vs => vs = u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u9 :: u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pushValStep hK (hpush main) (u9) (u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (hFfac) hVs50) hVW)
      have c2H4 : WordR main _ (fun vs => vs = u9 :: u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        binStepP hK (hmulS main) (((Ffac : ℕ) : ℤ)) (((k + 1 : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((Ffac * (k + 1) : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost4 hW2 hSB30 hKmulS (iszV (hFfac) hWs50) (iszV (hk1) hWs12))
      have c2P40 : vsz (u10) ≤ V := (vszV (hFk) hVsFk)
      have c2P41 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
      have c2S : vsh 2 (u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 2 * V := by
        rw [vsh_cons, vsh_cons, vsh_zero]
        exact le_trans (Nat.add_le_add (c2P40) (Nat.add_le_add (c2P41) (le_refl 0))) (le_of_eq (by ring))
      have c2H5 : WordR main _ (fun vs => vs = u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v32 :: u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pickStep hK (hpick main) (1) (u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW c2S (le_trans (by norm_num : 2 ≤ 100) hW100)))
      have c2H6 : WordR main _ (fun vs => vs = v32 :: u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u11 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        binStepP hK (hadd main) (((upar n : ℕ) : ℤ)) (((Ffac * (k + 1) : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((upar n + Ffac * (k + 1) : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd (iszV (hupar) hWs50) (iszV (hFk) hWsFk))
      have bH1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        dupStep hK (hdup main) (.int ((k : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdup (vszV (hk11) hVs11) hVW)
      have bP10 : vsz (.int ((k : ℕ) : ℤ)) ≤ V := (vszV (hk11) hVs11)
      have bP11 : vsz (.int ((k : ℕ) : ℤ)) ≤ V := (vszV (hk11) hVs11)
      have bP12 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
      have bP13 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
      have bS : vsh 4 (.int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
        rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
        exact le_trans (Nat.add_le_add (bP10) (Nat.add_le_add (bP11) (Nat.add_le_add (bP12) (Nat.add_le_add (bP13) (le_refl 0))))) (le_of_eq (by ring))
      have bH2 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v20 :: .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pickStep hK (hpick main) (3) (.int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 9) (Nat.le_add_left 9 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW bS (le_trans (by norm_num : 4 ≤ 100) hW100)))
      have bH3 : WordR main _ (fun vs => vs = v20 :: .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: v20 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        swapStep hK (hswap main) (v20) (.int ((k : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost2 hW2 hSB30 hKswap (vszV (hdpar) hVs50) (vszV (hk11) hVs11) hVW)
      have bH4 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v20 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int (if ((k : ℤ) < (dpar n : ℤ)) then 1 else 0) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        binStepP hK (hlt main) (((k : ℕ) : ℤ)) (((dpar n : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (by trivial) ((if ((k : ℤ) < (dpar n : ℤ)) then 1 else 0)) rfl (W ^ 30) (cost6 hW2 hSB30 hKlt (iszV (hk11) hWs11) (iszV (hdpar) hWs50))
      have c1ch := fun (hcond : dpar n ≤ k) => by
        have c1H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          dupStep hK (hdup main) (.int ((k : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdup (vszV (hk11) hVs11) hVW)
        have c1P10 : vsz (.int ((k : ℕ) : ℤ)) ≤ V := (vszV (hk11) hVs11)
        have c1P11 : vsz (.int ((k : ℕ) : ℤ)) ≤ V := (vszV (hk11) hVs11)
        have c1P12 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
        have c1P13 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
        have c1S : vsh 4 (.int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
          rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
          exact le_trans (Nat.add_le_add (c1P10) (Nat.add_le_add (c1P11) (Nat.add_le_add (c1P12) (Nat.add_le_add (c1P13) (le_refl 0))))) (le_of_eq (by ring))
        have c1H2 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v20 :: .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pickStep hK (hpick main) (3) (.int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 9) (Nat.le_add_left 9 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW c1S (le_trans (by norm_num : 4 ≤ 100) hW100)))
        have c1H3 : WordR main _ (fun vs => vs = v20 :: .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: v20 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          swapStep hK (hswap main) (v20) (.int ((k : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost2 hW2 hSB30 hKswap (vszV (hdpar) hVs50) (vszV (hk11) hVs11) hVW)
        have c1H4 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v20 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u1 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hsub main) (((k : ℕ) : ℤ)) (((dpar n : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((k - dpar n : ℕ) : ℤ)) (by rw [Nat.cast_sub hcond]) (W ^ 30) (cost6 hW2 hSB30 hKsub (iszV (hk11) hWs11) (iszV (hdpar) hWs50))
        have c1H5 : WordR main _ (fun vs => vs = u1 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((1 : ℕ) : ℤ) :: u1 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (.int ((1 : ℕ) : ℤ)) (u1 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h1) hVs50) hVW)
        have c1H6 : WordR main _ (fun vs => vs = .int ((1 : ℕ) : ℤ) :: u1 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u2 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hadd main) (((1 : ℕ) : ℤ)) (((k - dpar n : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((k - dpar n + 1 : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd (iszV (h1) hWs50) (iszV (hkdp) hWs11))
        have c1H7 : WordR main _ (fun vs => vs = u2 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u3 :: u2 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (u3) (u2 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h2F) hVs50) hVW)
        have c1H8 : WordR main _ (fun vs => vs = u3 :: u2 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u4 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hmulS main) (((2 * Ffac : ℕ) : ℤ)) (((k - dpar n + 1 : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((2 * Ffac * (k - dpar n + 1) : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost4 hW2 hSB30 hKmulS (iszV (h2F) hWs50) (iszV (hkdp1) hWs12))
        have c1H9 : WordR main _ (fun vs => vs = u4 :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          swapStep hK (hswap main) (u4) (.int ((k : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost2 hW2 hSB30 hKswap (vszV (h2Fk) hVsFk) (vszV (hk11) hVs11) hVW)
        have c1H10 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          dropStep hK (hdrop main) (.int ((k : ℕ) : ℤ)) (u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdrop (vszV (hk11) hVs11) hVW)
        have c1P100 : vsz (u4) ≤ V := (vszV (h2Fk) hVsFk)
        have c1P101 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
        have c1S : vsh 2 (u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 2 * V := by
          rw [vsh_cons, vsh_cons, vsh_zero]
          exact le_trans (Nat.add_le_add (c1P100) (Nat.add_le_add (c1P101) (le_refl 0))) (le_of_eq (by ring))
        have c1H11 : WordR main _ (fun vs => vs = u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v32 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pickStep hK (hpick main) (1) (u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW c1S (le_trans (by norm_num : 2 ≤ 100) hW100)))
        have c1H12 : WordR main _ (fun vs => vs = v32 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((2 : ℕ) : ℤ) :: v32 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (.int ((2 : ℕ) : ℤ)) (v32 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h2c) hVs50) hVW)
        have c1H13 : WordR main _ (fun vs => vs = .int ((2 : ℕ) : ℤ) :: v32 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u5 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hmulS main) (((2 : ℕ) : ℤ)) (((upar n : ℕ) : ℤ)) (u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((2 * upar n : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost4 hW2 hSB30 hKmulS (iszV (h2c) hWs50) (iszV (hupar) hWs50))
        have c1H14 : WordR main _ (fun vs => vs = u5 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int (-1 : ℤ) :: u5 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (.int (-1 : ℤ)) (u5 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszVneg h1 hVs50) hVW)
        have c1H15 : WordR main _ (fun vs => vs = .int (-1 : ℤ) :: u5 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u6 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hadd main) ((-1 : ℤ)) (((2 * upar n : ℕ) : ℤ)) (u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((2 * upar n - 1 : ℕ) : ℤ)) (by rw [Nat.cast_sub (show (1:ℕ) ≤ 2 * upar n by omega)]; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd hneg1isz (iszV (h2u) hWs24))
        have c1H16 : WordR main _ (fun vs => vs = u6 :: u4 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u7 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hadd main) (((2 * upar n - 1 : ℕ) : ℤ)) (((2 * Ffac * (k - dpar n + 1) : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1) : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd (iszV (h2u1) hWs24) (iszV (h2Fk) hWsFk))
        exact conseqC hK (seqC hK (seqC hK (seqC hK (seqC hK (c1H1) (c1H2)) (seqC hK (c1H3) (c1H4))) (seqC hK (seqC hK (c1H5) (c1H6)) (seqC hK (c1H7) (c1H8)))) (seqC hK (seqC hK (seqC hK (c1H9) (c1H10)) (seqC hK (c1H11) (c1H12))) (seqC hK (seqC hK (c1H13) (c1H14)) (seqC hK (c1H15) (c1H16))))) (sum_branchN (n := 16) hW100 (by norm_num) (by omega))
      have c2ch := by
        have c2H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((1 : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (.int ((1 : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h1) hVs50) hVW)
        have c2H2 : WordR main _ (fun vs => vs = .int ((1 : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hadd main) (((1 : ℕ) : ℤ)) (((k : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((k + 1 : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd (iszV (h1) hWs50) (iszV (hk11) hWs11))
        have c2H3 : WordR main _ (fun vs => vs = u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u9 :: u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (u9) (u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (hFfac) hVs50) hVW)
        have c2H4 : WordR main _ (fun vs => vs = u9 :: u8 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hmulS main) (((Ffac : ℕ) : ℤ)) (((k + 1 : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((Ffac * (k + 1) : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost4 hW2 hSB30 hKmulS (iszV (hFfac) hWs50) (iszV (hk1) hWs12))
        have c2P40 : vsz (u10) ≤ V := (vszV (hFk) hVsFk)
        have c2P41 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
        have c2S : vsh 2 (u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 2 * V := by
          rw [vsh_cons, vsh_cons, vsh_zero]
          exact le_trans (Nat.add_le_add (c2P40) (Nat.add_le_add (c2P41) (le_refl 0))) (le_of_eq (by ring))
        have c2H5 : WordR main _ (fun vs => vs = u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v32 :: u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pickStep hK (hpick main) (1) (u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 1 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 2 ≤ 100) hW100) (pick_sum_le hW4 hVW c2S (le_trans (by norm_num : 2 ≤ 100) hW100)))
        have c2H6 : WordR main _ (fun vs => vs = v32 :: u10 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u11 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hadd main) (((upar n : ℕ) : ℤ)) (((Ffac * (k + 1) : ℕ) : ℤ)) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by trivial)) (((upar n + Ffac * (k + 1) : ℕ) : ℤ)) (by push_cast; ring) (W ^ 30) (cost6 hW2 hSB30 hKadd (iszV (hupar) hWs50) (iszV (hFk) hWsFk))
        exact conseqC hK (seqC hK (seqC hK (c2H1) (seqC hK (c2H2) (c2H3))) (seqC hK (c2H4) (seqC hK (c2H5) (c2H6)))) (sum_branchN (n := 6) hW100 (by norm_num) (by omega))
      have hbr1 := fun (hz0 : (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) = 0) => by
        have hcond : dpar n ≤ k := by
          by_contra hlt
          have h1 : ((k:ℤ) < (dpar n : ℤ)) := by exact_mod_cast (not_le.mp hlt)
          rw [if_pos h1] at hz0
          exact absurd hz0 (by norm_num)
        exact c1ch hcond
      have hbr2 := fun (hzne : (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) ≠ 0) => by
        have hcond : k < dpar n := by
          by_contra hlt
          have h1 : ¬ ((k:ℤ) < (dpar n : ℤ)) := by
            intro hc
            exact hlt (by exact_mod_cast hc)
          rw [if_neg h1] at hzne
          exact hzne rfl
        exact c2ch
      have hraw := hifZero main _ _ (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) (.int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) _ _ (W ^ 32) (W ^ 32) hbr1 hbr2
      have hz2 : WordR main _ (fun vs => vs = .int (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
          (fun _ out => out = if (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) = 0 then u7 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R else u11 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => W ^ 34) :=
        conseqC hK (ifZeroStep hK hraw) (cost7c hW2 (le_refl _) hKifZero (le_trans (isz_ite_le3 _) (le_trans (by norm_num : (3:ℕ) ≤ 11 + 2) hVs11)) hVW (max_le (le_refl _) (le_refl _)))
      have hz3 : WordR main _ (fun vs => vs = .int (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) :: .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
          (fun _ out => out = if k < dpar n then u11 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R else u7 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => W ^ 34) :=
        step_rw hK hz2 (ite_lt_swap (u7 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (u11 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R))
      have chb := seqC hK (seqC hK (bH1) (bH2)) (seqC hK (bH3) (seqC hK (bH4) (hz3)))
      refine hK.conseq main (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP))))))))) (fun vs => vs = .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun vs => vs = .int ((k : ℕ) : ℤ) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
        (fun _ out => out = (if k < dpar n then u11 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R else u7 :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R))
        (fun _ out => ∃ y, out = y :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R ∧
          (∃ k' : ℕ, Val.int (k:ℤ) = Val.int (k':ℤ) ∧ y = Val.int ((ssPar n).getD k' 0 : ℤ)) ∧ vsz y ≤ V)
        _ (fun _ => W ^ 35) chb (fun _ h => h) ?_ ?_
      · rintro vs out _ hout
        rw [hout, cons_ite]
        refine ⟨_, rfl, ⟨k, rfl, ?_⟩, ?_⟩
        · by_cases h : k < dpar n
          · rw [if_pos h, ssPar_getD_sswindow n k hkD, if_pos h]
          · rw [if_neg h, ssPar_getD_sswindow n k hkD, if_neg h]
        · by_cases h : k < dpar n
          · rw [if_pos h]; exact vszV huk hVsUk
          · rw [if_neg h]; exact vszV hres1 hVsUk
      · intro vs _
        exact sum_body hW100 (by ring)
    have hxs : ∀ x ∈ (List.range D).map (fun k : ℕ => Val.int (k:ℤ)),
        (∃ k : ℕ, k < D ∧ x = Val.int (k:ℤ)) ∧ vsz x ≤ V := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [List.mem_range] at hk
      exact ⟨⟨k, hk, rfl⟩, vszV (show k.size ≤ 11 from Nat.size_le.mpr (lt_of_lt_of_le hk (by norm_num [HvdH.D]))) hVs11⟩
    have hml := hmapList main (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP))))))))) (v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) _ _ (W ^ 35) V hbody ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) hxs
    refine hK.conseq main (mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP)))))))))) (fun vs => vs = intList2 (List.range D) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
      (fun vs => vs = ofList ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
      (fun _ out => ∃ ys, out = ofList ys :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R ∧
        List.Forall₂ (fun x y => ∃ k : ℕ, x = Val.int (k:ℤ) ∧ y = Val.int ((ssPar n).getD k 0 : ℤ))
          ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) ys)
      (fun _ out => out = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) _ SB hml ?_ ?_ ?_
    · intro vs h; rw [h]; rfl
    · rintro vs out _ ⟨ys, rfl, hrel⟩; rw [forall₂_ss hrel, intList_eq_intList2]
    · intro vs _; exact cost8 hW4 hSB37 hDleW (le_refl _) hKmapList hVW
  have CHAIN := seqC hK (H65) (H66)
  exact conseqC hK CHAIN ((Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))))

theorem seg3
    (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (main : Cmd) (n : ℕ) (R : List Val)
    (dupP : Cmd)
    (Kdup : ℕ)
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest) (fun vs => Kdup * (vsz (vs.headD .nil) + 1)))
    (dropP : Cmd)
    (Kdrop : ℕ)
    (hdrop : ∀ main : Cmd, WordR main dropP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest) (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (swapP : Cmd)
    (Kswap : ℕ)
    (hswap : ∀ main : Cmd, WordR main swapP (fun vs => 2 ≤ vs.length) (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest) (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (pickP : ℕ → Cmd)
    (Kpick : ℕ)
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs) (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (rollP : ℕ → Cmd)
    (Kroll : ℕ)
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k) (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (pushP : Val → Cmd)
    (Kpush : ℕ)
    (hpush : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs) (fun _ => Kpush * (vsz v + 1)))
    (ifZeroP : Cmd → Cmd → Cmd)
    (KifZero : ℕ)
    (hifZero : ∀ (main q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ), (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) → (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) → WordR main (ifZeroP q₁ q₂) (fun vs => vs = .int z :: rest) (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => KifZero * (isz z + 1) + max c₁ c₂))
    (mapListP : Cmd → Cmd)
    (KmapList : ℕ)
    (hmapList : ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ), (∀ x : Val, P x → WordR main q (fun vs => vs = x :: rest) (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) → ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) → WordR main (mapListP q) (fun vs => vs = ofList xs :: rest) (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys) (fun _ => xs.length * (c + KmapList * (L + 1)) + KmapList))
    (addP : Cmd)
    (Kadd : ℕ)
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (fun a b => a + b) (fun a b => Kadd * (isz a + isz b)))
    (subP : Cmd)
    (Ksub : ℕ)
    (hsub : ∀ main : Cmd, BinOp main subP (fun _ _ => True) (fun a b => a - b) (fun a b => Ksub * (isz a + isz b)))
    (negP : Cmd)
    (Kneg : ℕ)
    (hneg : ∀ main : Cmd, UnOp main negP (fun _ => True) (fun a => -a) (fun a => Kneg * isz a))
    (ltP : Cmd)
    (Klt : ℕ)
    (hlt : ∀ main : Cmd, BinOp main ltP (fun _ _ => True) (fun a b => if a < b then 1 else 0) (fun a b => Klt * (isz a + isz b)))
    (mulSP : Cmd)
    (KmulS : ℕ)
    (hmulS : ∀ main : Cmd, BinOp main mulSP (fun _ _ => True) (fun a b => a * b) (fun a b => KmulS * isz a * isz b))
    (fdivP : Cmd)
    (Kfdiv : ℕ)
    (hfdiv : ∀ main : Cmd, BinOp main fdivP (fun a b => 0 < b) Int.fdiv (fun a b => Kfdiv * isz a * isz b))
    (sqrtP : Cmd)
    (Ksqrt : ℕ)
    (hsqrt : ∀ main : Cmd, UnOp main sqrtP (fun a => 0 ≤ a) (fun a => ↑a.toNat.sqrt) (fun a => Ksqrt * isz a ^ 2))
    (clog2P : Cmd)
    (Kclog2 : ℕ)
    (hclog2 : ∀ main : Cmd, UnOp main clog2P (fun a => 0 ≤ a) (fun a => ↑(Nat.clog 2 a.toNat)) (fun a => Kclog2 * isz a))
    (pow2P : Cmd)
    (Kpow2 : ℕ)
    (hpow2 : ∀ main : Cmd, UnOp main pow2P (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat) (fun k => Kpow2 * (k.toNat + isz k)))
    (Ksum K0 B W V SB : ℕ)
    (hKsumdef : Ksum = Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + KifZero + KmapList + Kadd + Ksub + Kneg + Klt + KmulS + Kfdiv + Ksqrt + Kclog2 + Kpow2)
    (hK0def : K0 = Ksum + 2 ^ 44 + 100)
    (hBdef : B = n.size + 1)
    (hVdef : V = (KBsz + n.size + 6) * (D + 2))
    (hWdef : W = B ^ K0)
    (hSBdef : SB = W ^ 40)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hsz : 65755586 ≤ n.size)
    (hn2 : 1 < n)
    (hK0pos : 1 ≤ K0)
    (hK0ge : 2 ^ 44 + 100 ≤ K0)
    (hB2 : 2 ≤ B)
    (hVdef2 : V = (KBsz + n.size + 6) * (D + 2))
    (hW2 : 2 ≤ W)
    (hW4 : 4 ≤ W)
    (hW100 : 100 ≤ W)
    (hVW : V + 1 ≤ W)
    (hVsz : n.size + 100 ≤ V)
    (hK0W : K0 ≤ W)
    (hKdupW : Kdup ≤ W)
    (hKdropW : Kdrop ≤ W)
    (hKswapW : Kswap ≤ W)
    (hKpickW : Kpick ≤ W)
    (hKrollW : Kroll ≤ W)
    (hKpushW : Kpush ≤ W)
    (hKifZeroW : KifZero ≤ W)
    (hKmapListW : KmapList ≤ W)
    (hKaddW : Kadd ≤ W)
    (hKsubW : Ksub ≤ W)
    (hKnegW : Kneg ≤ W)
    (hKltW : Klt ≤ W)
    (hKmulSW : KmulS ≤ W)
    (hKfdivW : Kfdiv ≤ W)
    (hKsqrtW : Ksqrt ≤ W)
    (hKclog2W : Kclog2 ≤ W)
    (hKpow2W : Kpow2 ≤ W)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hW77 : 77 ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hSB20 : W ^ 20 ≤ SB)
    (hSB30 : W ^ 20 ≤ W ^ 30)
    (hSB34 : W ^ 34 ≤ W ^ 34)
    (hSB37 : W ^ 37 ≤ SB)
    (hbparT : (bpar n).size ≤ n.size + 4)
    (hpparT : (ppar n).size ≤ n.size + 4)
    (haparT : (apar n).size ≤ n.size + 4)
    (hkTparT : (kTpar n).size ≤ n.size + 4)
    (hTparT : (Tpar n).size ≤ n.size + 4)
    (hkrparT : (krpar n).size ≤ n.size + 4)
    (hrparT : (rpar n).size ≤ n.size + 4)
    (hdparT : (dpar n).size ≤ n.size + 4)
    (hLparT : (Lpar n).size ≤ n.size + 4)
    (huparT : (upar n).size ≤ n.size + 4)
    (hNsz : n.size ≤ n.size + 50)
    (hbpar : (bpar n).size ≤ n.size + 50)
    (hppar : (ppar n).size ≤ n.size + 50)
    (hapar : (apar n).size ≤ n.size + 50)
    (hkTpar : (kTpar n).size ≤ n.size + 50)
    (hTpar : (Tpar n).size ≤ n.size + 50)
    (hkrpar : (krpar n).size ≤ n.size + 50)
    (hrpar : (rpar n).size ≤ n.size + 50)
    (hdpar : (dpar n).size ≤ n.size + 50)
    (hLpar : (Lpar n).size ≤ n.size + 50)
    (hupar : (upar n).size ≤ n.size + 50)
    (hupar4 : (upar n).size ≤ n.size + 4)
    (h6c : (6:ℕ).size ≤ n.size + 50)
    (h1 : (1:ℕ).size ≤ n.size + 50)
    (h2c : (2:ℕ).size ≤ n.size + 50)
    (h4c : (4:ℕ).size ≤ n.size + 50)
    (hD : (D:ℕ).size ≤ n.size + 50)
    (hDv : (D:ℕ).size ≤ 11)
    (hDm1 : (D - 1).size ≤ n.size + 50)
    (h2Dm1v : (2 * D - 1).size ≤ 13)
    (h2Dm1 : (2 * D - 1).size ≤ n.size + 50)
    (h4Dv : (4 * D).size ≤ 14)
    (h4D : (4 * D).size ≤ n.size + 50)
    (hFfacT : (Ffac).size ≤ n.size + 4)
    (hQallT : (Qall).size ≤ n.size + 4)
    (hFfac : (Ffac).size ≤ n.size + 50)
    (hFfac4 : (Ffac).size ≤ n.size + 4)
    (hQall : (Qall).size ≤ n.size + 50)
    (hFQ3 : (Ffac * Qall).size ≤ n.size + 4)
    (hFQ : (Ffac * Qall).size ≤ n.size + 50)
    (hK13 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hK1 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (h2Fv : (2 * Ffac).size ≤ n.size + 4)
    (h2F : (2 * Ffac).size ≤ n.size + 50)
    (h2F4 : (2 * Ffac).size ≤ n.size + 4)
    (hDD : (12 * D * D).size ≤ 26)
    (hDDbT : (12 * D * D * bpar n).size ≤ n.size + 30)
    (hDDb : (12 * D * D * bpar n).size ≤ n.size + 50)
    (hDDb1 : (12 * D * D * bpar n - 1).size ≤ n.size + 50)
    (hSQ1 : (Nat.sqrt (12 * D * D * bpar n - 1)).size ≤ n.size + 50)
    (hSQ2 : (Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1))).size ≤ n.size + 50)
    (hN4T : (4 * n).size ≤ n.size + 3)
    (hN4 : (4 * n).size ≤ n.size + 50)
    (hN4bT : (4 * n + bpar n).size ≤ n.size + 5)
    (hN4b : (4 * n + bpar n).size ≤ n.size + 50)
    (hN4b1 : (4 * n + bpar n - 1).size ≤ n.size + 50)
    (hQVT : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 5)
    (hQV : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 50)
    (hDKRT : (D * krpar n).size ≤ n.size + 20)
    (hDKR : (D * krpar n).size ≤ n.size + 50)
    (hR2D1T : (rpar n * (2 * D - 1)).size ≤ n.size + 20)
    (hR2D1 : (rpar n * (2 * D - 1)).size ≤ n.size + 50)
    (hR4D : (rpar n * (2 * D - 1) / (4 * D)).size ≤ n.size + 50)
    (hLK1T : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 5)
    (hLK1 : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (hMMT : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 5)
    (hMM : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 50)
    (hMFQ : (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall)).size ≤ n.size + 50)
    (hVLD : vsz (HvdH.intList (List.range D)) ≤ V)
    (hVss : vsz (HvdH.intList (ssPar n)) ≤ V)
    (hVts : vsz (HvdH.intList (tsPar n)) ≤ V)
    (hVLD2 : vsz (intList2 (List.range D)) ≤ V)
    (hVssl : vsz (intList2 (ssPar n)) ≤ V)
    (hVtsl : vsz (intList2 (tsPar n)) ≤ V)
    (hDleW : D ≤ W)
    (hbparposN : 0 < bpar n)
    (hkTw : kTpar n ≤ W)
    (hkrw : krpar n ≤ W)
    (hLpos : 0 < Lpar n)
    (huparpos : 0 < upar n)
    (hposDDb : 0 < 12 * D * D * bpar n)
    (hposN4b : 0 < 4 * n + bpar n)
    (hneg1isz : isz (-1 : ℤ) ≤ W)
    (Hbparpos : (0:ℤ) < (bpar n : ℤ))
    (Hdpos : (0:ℤ) < (D : ℤ))
    (H4Dpos : (0:ℤ) < (4 * D : ℤ))
    (HFQpos : (0:ℤ) < (Ffac * Qall : ℤ))
    (hDle : HvdH.D ≤ 2 ^ 11)
    (hVs26 : (26:ℕ) + 2 ≤ V)
    (hVs51 : n.size + 50 + 1 + 2 ≤ V)
    (hVs11 : (11:ℕ) + 2 ≤ V)
    (hVs12 : (12:ℕ) + 2 ≤ V)
    (hVs24 : ((n.size + 4) + 2) + 2 ≤ V)
    (hVsFk : ((n.size + 4) + 12) + 2 ≤ V)
    (hVsUk : (((n.size + 4) + 12) + 1) + 2 ≤ V)
    (hVs50 : n.size + 50 + 2 ≤ V)
    (hVWle : V ≤ W)
    (hWs26 : (26:ℕ) + 2 ≤ W)
    (hWs51 : n.size + 50 + 1 + 2 ≤ W)
    (hWs11 : (11:ℕ) + 2 ≤ W)
    (hWs12 : (12:ℕ) + 2 ≤ W)
    (hWs24 : ((n.size + 4) + 2) + 2 ≤ W)
    (hWsFk : ((n.size + 4) + 12) + 2 ≤ W)
    (hWsUk : (((n.size + 4) + 12) + 1) + 2 ≤ W)
    (hWs50 : n.size + 50 + 2 ≤ W)
    (hc6 : Nat.size 6 ≤ n.size + 4)
    (hcDD : (12 * D * D).size ≤ n.size + 4)
    (hc1 : Nat.size 1 ≤ n.size + 4)
    (hc4 : Nat.size 4 ≤ n.size + 4)
    (hcDm1 : (D - 1).size ≤ n.size + 4)
    (hcDz : D.size ≤ n.size + 4)
    (hc2Dm1 : (2 * D - 1).size ≤ n.size + 4)
    (hc4D : (4 * D).size ≤ n.size + 4)
    (hcF : Ffac.size ≤ n.size + 4)
    (hcQ : Qall.size ≤ n.size + 4)
    (hcFQ : (Ffac * Qall).size ≤ n.size + 4)
    (hcK1z : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hc2F : (2 * Ffac).size ≤ n.size + 4)
    :
    WordR main (Cmd.seq ((pushP (intList2 (List.range D)))) ((mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP)))))))))))) (fun vs => vs = intList2 (ssPar n) :: .int ((upar n : ℕ) : ℤ) :: .int ((dpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((bpar n : ℕ) : ℤ) :: R) (fun _ out => out = intList2 (tsPar n) :: intList2 (ssPar n) :: .int ((upar n : ℕ) : ℤ) :: .int ((dpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((bpar n : ℕ) : ℤ) :: R) (fun _ => 2 * SB) := by
  let v1 : Val := .int ((bpar n : ℕ) : ℤ)
  let v2 : Val := .int ((ppar n : ℕ) : ℤ)
  let v3 : Val := .int ((12 * D * D : ℕ) : ℤ)
  let v4 : Val := .int ((12 * D * D * bpar n : ℕ) : ℤ)
  let v5 : Val := .int ((12 * D * D * bpar n - 1 : ℕ) : ℤ)
  let v6 : Val := .int ((Nat.sqrt (12 * D * D * bpar n - 1) : ℕ) : ℤ)
  let v7 : Val := .int ((Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1)) : ℕ) : ℤ)
  let v8 : Val := .int ((apar n : ℕ) : ℤ)
  let v9 : Val := .int ((4 * n : ℕ) : ℤ)
  let v10 : Val := .int ((4 * n + bpar n : ℕ) : ℤ)
  let v11 : Val := .int ((4 * n + bpar n - 1 : ℕ) : ℤ)
  let v12 : Val := .int (((4 * n + bpar n - 1) / bpar n : ℕ) : ℤ)
  let v13 : Val := .int ((kTpar n : ℕ) : ℤ)
  let v14 : Val := .int ((Tpar n : ℕ) : ℤ)
  let v15 : Val := .int ((D - 1 : ℕ) : ℤ)
  let v16 : Val := .int ((kTpar n + (D - 1) : ℕ) : ℤ)
  let v17 : Val := .int ((krpar n : ℕ) : ℤ)
  let v18 : Val := .int ((rpar n : ℕ) : ℤ)
  let v19 : Val := .int ((D * krpar n : ℕ) : ℤ)
  let v20 : Val := .int ((dpar n : ℕ) : ℤ)
  let v21 : Val := .int (((2 * D - 1) : ℕ) : ℤ)
  let v22 : Val := .int ((rpar n * (2 * D - 1) : ℕ) : ℤ)
  let v23 : Val := .int (((4 * D) : ℕ) : ℤ)
  let v24 : Val := .int ((rpar n * (2 * D - 1) / (4 * D) : ℕ) : ℤ)
  let v25 : Val := .int ((Lpar n : ℕ) : ℤ)
  let v26 : Val := .int ((Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v27 : Val := .int ((Lpar n + Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v28 : Val := .int ((Ffac * Qall : ℕ) : ℤ)
  let v29 : Val := .int (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall) : ℕ) : ℤ)
  let v30 : Val := .int ((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall) : ℕ) : ℤ)
  let v31 : Val := .int ((Qall : ℕ) : ℤ)
  let v32 : Val := .int ((upar n : ℕ) : ℤ)
  have H67 : WordR main _ (fun vs => vs = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (List.range D) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    pushValStep hK (hpush main) (intList2 (List.range D)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKpush hVLD2 hVW)
  have H68 : WordR main (mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP)))))))))) (fun vs => vs = intList2 (List.range D) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (tsPar n) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => SB) := by
    have hbody : ∀ x : Val, (∃ k : ℕ, k < D ∧ x = Val.int (k:ℤ)) →
        WordR main (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP))))))))) (fun vs => vs = x :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
          (fun _ out => ∃ y, out = y :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R ∧
            (∃ k' : ℕ, x = Val.int (k':ℤ) ∧ y = Val.int ((tsPar n).getD k' 0 : ℤ)) ∧ vsz y ≤ V)
          (fun _ => W ^ 35) := by
      intro x hx
      obtain ⟨k, hkD, rfl⟩ := hx
      let u1 : Val := .int ((rpar n / 2 : ℕ) : ℤ)
      have hk11 : k.size ≤ 11 := Nat.size_le.mpr (lt_of_lt_of_le hkD hDle)
      have h2sz : (2:ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
      have hk1 : (k + 1).size ≤ 12 := le_trans (size_succ_le k) (le_trans (Nat.add_le_add_right hk11 1) (by norm_num))
      have hFk : (Ffac * (k + 1)).size ≤ (n.size + 4) + 12 := le_trans (size_mul_le Ffac (k + 1)) (Nat.add_le_add hFfac4 hk1)
      have huk : (upar n + Ffac * (k + 1)).size ≤ ((n.size + 4) + 12) + 1 := le_trans (szAdd_le (upar n) (Ffac * (k + 1))) (Nat.add_le_add_right (max_le (le_trans hupar4 (Nat.le_add_right (n.size + 4) 12)) hFk) 1)
      have hkdp : (k - dpar n).size ≤ 11 := le_trans (szSub_le k (dpar n)) hk11
      have hkdp1 : (k - dpar n + 1).size ≤ 12 := le_trans (size_succ_le (k - dpar n)) (le_trans (Nat.add_le_add_right hkdp 1) (by norm_num))
      have h2Fk : (2 * Ffac * (k - dpar n + 1)).size ≤ (n.size + 4) + 12 := le_trans (size_mul_le (2 * Ffac) (k - dpar n + 1)) (Nat.add_le_add h2F4 hkdp1)
      have h2u : (2 * upar n).size ≤ (n.size + 4) + 2 := le_trans (size_mul_le 2 (upar n)) (le_trans (Nat.add_le_add h2sz hupar4) (le_of_eq (Nat.add_comm 2 (n.size + 4))))
      have h2u1 : (2 * upar n - 1).size ≤ (n.size + 4) + 2 := le_trans (szSub_le (2 * upar n) 1) h2u
      have hres1 : (2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1)).size ≤ ((n.size + 4) + 12) + 1 := le_trans (szAdd_le (2 * upar n - 1) (2 * Ffac * (k - dpar n + 1))) (Nat.add_le_add_right (max_le (le_trans h2u1 (Nat.add_le_add_left (by norm_num) (n.size + 4))) h2Fk) 1)
      have d1H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        dropStep hK (hdrop main) (.int ((k : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdrop (vszV (hk11) hVs11) hVW)
      have d1P10 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
      have d1P11 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
      have d1P12 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
      have d1P13 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
      have d1S : vsh 4 (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
        rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
        exact le_trans (Nat.add_le_add (d1P10) (Nat.add_le_add (d1P11) (Nat.add_le_add (d1P12) (Nat.add_le_add (d1P13) (le_refl 0))))) (le_of_eq (by ring))
      have d1H2 : WordR main _ (fun vs => vs = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pickStep hK (hpick main) (3) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW d1S (le_trans (by norm_num : 4 ≤ 100) hW100)))
      have d2H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        dropStep hK (hdrop main) (.int ((k : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdrop (vszV (hk11) hVs11) hVW)
      have d2P10 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
      have d2P11 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
      have d2P12 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
      have d2P13 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
      have d2S : vsh 4 (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
        rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
        exact le_trans (Nat.add_le_add (d2P10) (Nat.add_le_add (d2P11) (Nat.add_le_add (d2P12) (Nat.add_le_add (d2P13) (le_refl 0))))) (le_of_eq (by ring))
      have d2H2 : WordR main _ (fun vs => vs = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pickStep hK (hpick main) (3) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW d2S (le_trans (by norm_num : 4 ≤ 100) hW100)))
      have d2H3 : WordR main _ (fun vs => vs = v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((2 : ℕ) : ℤ) :: v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pushValStep hK (hpush main) (.int ((2 : ℕ) : ℤ)) (v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h2c) hVs50) hVW)
      have d2H4 : WordR main _ (fun vs => vs = .int ((2 : ℕ) : ℤ) :: v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: .int ((2 : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        swapStep hK (hswap main) (.int ((2 : ℕ) : ℤ)) (v18) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost2 hW2 hSB30 hKswap (vszV (h2c) hVs50) (vszV (hrpar) hVs50) hVW)
      have d2H5 : WordR main _ (fun vs => vs = v18 :: .int ((2 : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u1 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        binStepP hK (hfdiv main) (((rpar n : ℕ) : ℤ)) (((2 : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by norm_num)) (((rpar n / 2 : ℕ) : ℤ)) (by rw [Int.ofNat_fdiv]) (W ^ 30) (cost4 hW2 hSB30 hKfdiv (iszV (hrpar) hWs50) (iszV (h2c) hWs50))
      have bH1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        dupStep hK (hdup main) (.int ((k : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdup (vszV (hk11) hVs11) hVW)
      have bP10 : vsz (.int ((k : ℕ) : ℤ)) ≤ V := (vszV (hk11) hVs11)
      have bP11 : vsz (.int ((k : ℕ) : ℤ)) ≤ V := (vszV (hk11) hVs11)
      have bP12 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
      have bP13 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
      have bP14 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
      have bS : vsh 5 (.int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 5 * V := by
        rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
        exact le_trans (Nat.add_le_add (bP10) (Nat.add_le_add (bP11) (Nat.add_le_add (bP12) (Nat.add_le_add (bP13) (Nat.add_le_add (bP14) (le_refl 0)))))) (le_of_eq (by ring))
      have bH2 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v20 :: .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        pickStep hK (hpick main) (4) (.int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 4 < 10) (Nat.le_add_left 10 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 5 ≤ 100) hW100) (pick_sum_le hW4 hVW bS (le_trans (by norm_num : 5 ≤ 100) hW100)))
      have bH3 : WordR main _ (fun vs => vs = v20 :: .int ((k : ℕ) : ℤ) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((k : ℕ) : ℤ) :: v20 :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        swapStep hK (hswap main) (v20) (.int ((k : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost2 hW2 hSB30 hKswap (vszV (hdpar) hVs50) (vszV (hk11) hVs11) hVW)
      have bH4 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: v20 :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int (if ((k : ℤ) < (dpar n : ℤ)) then 1 else 0) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
        binStepP hK (hlt main) (((k : ℕ) : ℤ)) (((dpar n : ℕ) : ℤ)) (.int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (by trivial) ((if ((k : ℤ) < (dpar n : ℤ)) then 1 else 0)) rfl (W ^ 30) (cost6 hW2 hSB30 hKlt (iszV (hk11) hWs11) (iszV (hdpar) hWs50))
      have c1ch := by
        have d1H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          dropStep hK (hdrop main) (.int ((k : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdrop (vszV (hk11) hVs11) hVW)
        have d1P10 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
        have d1P11 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
        have d1P12 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
        have d1P13 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
        have d1S : vsh 4 (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
          rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
          exact le_trans (Nat.add_le_add (d1P10) (Nat.add_le_add (d1P11) (Nat.add_le_add (d1P12) (Nat.add_le_add (d1P13) (le_refl 0))))) (le_of_eq (by ring))
        have d1H2 : WordR main _ (fun vs => vs = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pickStep hK (hpick main) (3) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW d1S (le_trans (by norm_num : 4 ≤ 100) hW100)))
        exact conseqC hK (seqC hK (d1H1) (d1H2)) (sum_branchN (n := 2) hW100 (by norm_num) (by omega))
      have c2ch := by
        have d2H1 : WordR main _ (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          dropStep hK (hdrop main) (.int ((k : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKdrop (vszV (hk11) hVs11) hVW)
        have d2P10 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
        have d2P11 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
        have d2P12 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
        have d2P13 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
        have d2S : vsh 4 (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
          rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
          exact le_trans (Nat.add_le_add (d2P10) (Nat.add_le_add (d2P11) (Nat.add_le_add (d2P12) (Nat.add_le_add (d2P13) (le_refl 0))))) (le_of_eq (by ring))
        have d2H2 : WordR main _ (fun vs => vs = intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pickStep hK (hpick main) (3) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 8) (Nat.le_add_left 8 R.length)) (W ^ 30) (cost3 hW2 hSB30 hKpick (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW d2S (le_trans (by norm_num : 4 ≤ 100) hW100)))
        have d2H3 : WordR main _ (fun vs => vs = v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = .int ((2 : ℕ) : ℤ) :: v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          pushValStep hK (hpush main) (.int ((2 : ℕ) : ℤ)) (v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost1 hW2 hSB30 hKpush (vszV (h2c) hVs50) hVW)
        have d2H4 : WordR main _ (fun vs => vs = .int ((2 : ℕ) : ℤ) :: v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: .int ((2 : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          swapStep hK (hswap main) (.int ((2 : ℕ) : ℤ)) (v18) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (W ^ 30) (cost2 hW2 hSB30 hKswap (vszV (h2c) hVs50) (vszV (hrpar) hVs50) hVW)
        have d2H5 : WordR main _ (fun vs => vs = v18 :: .int ((2 : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = u1 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (W ^ 30)) :=
          binStepP hK (hfdiv main) (((rpar n : ℕ) : ℤ)) (((2 : ℕ) : ℤ)) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ((by norm_num)) (((rpar n / 2 : ℕ) : ℤ)) (by rw [Int.ofNat_fdiv]) (W ^ 30) (cost4 hW2 hSB30 hKfdiv (iszV (hrpar) hWs50) (iszV (h2c) hWs50))
        exact conseqC hK (seqC hK (seqC hK (d2H1) (d2H2)) (seqC hK (d2H3) (seqC hK (d2H4) (d2H5)))) (sum_branchN (n := 5) hW100 (by norm_num) (by omega))
      have hbr1 := fun (hz0 : (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) = 0) => by
        have hcond : dpar n ≤ k := by
          by_contra hlt
          have h1 : ((k:ℤ) < (dpar n : ℤ)) := by exact_mod_cast (not_le.mp hlt)
          rw [if_pos h1] at hz0
          exact absurd hz0 (by norm_num)
        exact c1ch
      have hbr2 := fun (hzne : (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) ≠ 0) => by
        have hcond : k < dpar n := by
          by_contra hlt
          have h1 : ¬ ((k:ℤ) < (dpar n : ℤ)) := by
            intro hc
            exact hlt (by exact_mod_cast hc)
          rw [if_neg h1] at hzne
          exact hzne rfl
        exact c2ch
      have hraw := hifZero main _ _ (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) (.int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) _ _ (W ^ 32) (W ^ 32) hbr1 hbr2
      have hz2 : WordR main _ (fun vs => vs = .int (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
          (fun _ out => out = if (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) = 0 then v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R else u1 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => W ^ 34) :=
        conseqC hK (ifZeroStep hK hraw) (cost7c hW2 (le_refl _) hKifZero (le_trans (isz_ite_le3 _) (le_trans (by norm_num : (3:ℕ) ≤ 11 + 2) hVs11)) hVW (max_le (le_refl _) (le_refl _)))
      have hz3 : WordR main _ (fun vs => vs = .int (if ((k : ℤ) < (dpar n : ℤ)) then (1:ℤ) else 0) :: .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
          (fun _ out => out = if k < dpar n then u1 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R else v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => W ^ 34) :=
        step_rw hK hz2 (ite_lt_swap (v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (u1 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R))
      have chb := seqC hK (seqC hK (bH1) (bH2)) (seqC hK (bH3) (seqC hK (bH4) (hz3)))
      refine hK.conseq main (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP))))))))) (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun vs => vs = .int ((k : ℕ) : ℤ) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
        (fun _ out => out = (if k < dpar n then u1 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R else v18 :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R))
        (fun _ out => ∃ y, out = y :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R ∧
          (∃ k' : ℕ, Val.int (k:ℤ) = Val.int (k':ℤ) ∧ y = Val.int ((tsPar n).getD k' 0 : ℤ)) ∧ vsz y ≤ V)
        _ (fun _ => W ^ 35) chb (fun _ h => h) ?_ ?_
      · rintro vs out _ hout
        rw [hout, cons_ite]
        refine ⟨_, rfl, ⟨k, rfl, ?_⟩, ?_⟩
        · by_cases h : k < dpar n
          · rw [if_pos h, tsPar_getD_sswindow n k hkD, if_pos h]
          · rw [if_neg h, tsPar_getD_sswindow n k hkD, if_neg h]
        · by_cases h : k < dpar n
          · rw [if_pos h]; exact vszV (le_trans (szDiv_le (rpar n) 2) hrpar) hVs50
          · rw [if_neg h]; exact vszV hrpar hVs50
      · intro vs _
        exact sum_body hW100 (by ring)
    have hxs : ∀ x ∈ (List.range D).map (fun k : ℕ => Val.int (k:ℤ)),
        (∃ k : ℕ, k < D ∧ x = Val.int (k:ℤ)) ∧ vsz x ≤ V := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [List.mem_range] at hk
      exact ⟨⟨k, hk, rfl⟩, vszV (show k.size ≤ 11 from Nat.size_le.mpr (lt_of_lt_of_le hk (by norm_num [HvdH.D]))) hVs11⟩
    have hml := hmapList main (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP))))))))) (intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) _ _ (W ^ 35) V hbody ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) hxs
    refine hK.conseq main (mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP)))))))))) (fun vs => vs = intList2 (List.range D) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
      (fun vs => vs = ofList ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R)
      (fun _ out => ∃ ys, out = ofList ys :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R ∧
        List.Forall₂ (fun x y => ∃ k : ℕ, x = Val.int (k:ℤ) ∧ y = Val.int ((tsPar n).getD k 0 : ℤ))
          ((List.range D).map (fun k : ℕ => Val.int (k:ℤ))) ys)
      (fun _ out => out = intList2 (tsPar n) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) _ SB hml ?_ ?_ ?_
    · intro vs h; rw [h]; rfl
    · rintro vs out _ ⟨ys, rfl, hrel⟩; rw [forall₂_ts hrel, intList_eq_intList2]
    · intro vs _; exact cost8 hW4 hSB37 hDleW (le_refl _) hKmapList hVW
  have CHAIN := seqC hK (H67) (H68)
  exact conseqC hK CHAIN ((Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))))

theorem seg4
    (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (main : Cmd) (n : ℕ) (R : List Val)
    (dupP : Cmd)
    (Kdup : ℕ)
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest) (fun vs => Kdup * (vsz (vs.headD .nil) + 1)))
    (dropP : Cmd)
    (Kdrop : ℕ)
    (hdrop : ∀ main : Cmd, WordR main dropP (fun vs => vs ≠ []) (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest) (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (swapP : Cmd)
    (Kswap : ℕ)
    (hswap : ∀ main : Cmd, WordR main swapP (fun vs => 2 ≤ vs.length) (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest) (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (pickP : ℕ → Cmd)
    (Kpick : ℕ)
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs) (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (rollP : ℕ → Cmd)
    (Kroll : ℕ)
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k) (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (pushP : Val → Cmd)
    (Kpush : ℕ)
    (hpush : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs) (fun _ => Kpush * (vsz v + 1)))
    (ifZeroP : Cmd → Cmd → Cmd)
    (KifZero : ℕ)
    (hifZero : ∀ (main q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ), (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) → (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) → WordR main (ifZeroP q₁ q₂) (fun vs => vs = .int z :: rest) (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => KifZero * (isz z + 1) + max c₁ c₂))
    (mapListP : Cmd → Cmd)
    (KmapList : ℕ)
    (hmapList : ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ), (∀ x : Val, P x → WordR main q (fun vs => vs = x :: rest) (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) → ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) → WordR main (mapListP q) (fun vs => vs = ofList xs :: rest) (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys) (fun _ => xs.length * (c + KmapList * (L + 1)) + KmapList))
    (addP : Cmd)
    (Kadd : ℕ)
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (fun a b => a + b) (fun a b => Kadd * (isz a + isz b)))
    (subP : Cmd)
    (Ksub : ℕ)
    (hsub : ∀ main : Cmd, BinOp main subP (fun _ _ => True) (fun a b => a - b) (fun a b => Ksub * (isz a + isz b)))
    (negP : Cmd)
    (Kneg : ℕ)
    (hneg : ∀ main : Cmd, UnOp main negP (fun _ => True) (fun a => -a) (fun a => Kneg * isz a))
    (ltP : Cmd)
    (Klt : ℕ)
    (hlt : ∀ main : Cmd, BinOp main ltP (fun _ _ => True) (fun a b => if a < b then 1 else 0) (fun a b => Klt * (isz a + isz b)))
    (mulSP : Cmd)
    (KmulS : ℕ)
    (hmulS : ∀ main : Cmd, BinOp main mulSP (fun _ _ => True) (fun a b => a * b) (fun a b => KmulS * isz a * isz b))
    (fdivP : Cmd)
    (Kfdiv : ℕ)
    (hfdiv : ∀ main : Cmd, BinOp main fdivP (fun a b => 0 < b) Int.fdiv (fun a b => Kfdiv * isz a * isz b))
    (sqrtP : Cmd)
    (Ksqrt : ℕ)
    (hsqrt : ∀ main : Cmd, UnOp main sqrtP (fun a => 0 ≤ a) (fun a => ↑a.toNat.sqrt) (fun a => Ksqrt * isz a ^ 2))
    (clog2P : Cmd)
    (Kclog2 : ℕ)
    (hclog2 : ∀ main : Cmd, UnOp main clog2P (fun a => 0 ≤ a) (fun a => ↑(Nat.clog 2 a.toNat)) (fun a => Kclog2 * isz a))
    (pow2P : Cmd)
    (Kpow2 : ℕ)
    (hpow2 : ∀ main : Cmd, UnOp main pow2P (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat) (fun k => Kpow2 * (k.toNat + isz k)))
    (Ksum K0 B W V SB : ℕ)
    (hKsumdef : Ksum = Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + KifZero + KmapList + Kadd + Ksub + Kneg + Klt + KmulS + Kfdiv + Ksqrt + Kclog2 + Kpow2)
    (hK0def : K0 = Ksum + 2 ^ 44 + 100)
    (hBdef : B = n.size + 1)
    (hVdef : V = (KBsz + n.size + 6) * (D + 2))
    (hWdef : W = B ^ K0)
    (hSBdef : SB = W ^ 40)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hsz : 65755586 ≤ n.size)
    (hn2 : 1 < n)
    (hK0pos : 1 ≤ K0)
    (hK0ge : 2 ^ 44 + 100 ≤ K0)
    (hB2 : 2 ≤ B)
    (hVdef2 : V = (KBsz + n.size + 6) * (D + 2))
    (hW2 : 2 ≤ W)
    (hW4 : 4 ≤ W)
    (hW100 : 100 ≤ W)
    (hVW : V + 1 ≤ W)
    (hVsz : n.size + 100 ≤ V)
    (hK0W : K0 ≤ W)
    (hKdupW : Kdup ≤ W)
    (hKdropW : Kdrop ≤ W)
    (hKswapW : Kswap ≤ W)
    (hKpickW : Kpick ≤ W)
    (hKrollW : Kroll ≤ W)
    (hKpushW : Kpush ≤ W)
    (hKifZeroW : KifZero ≤ W)
    (hKmapListW : KmapList ≤ W)
    (hKaddW : Kadd ≤ W)
    (hKsubW : Ksub ≤ W)
    (hKnegW : Kneg ≤ W)
    (hKltW : Klt ≤ W)
    (hKmulSW : KmulS ≤ W)
    (hKfdivW : Kfdiv ≤ W)
    (hKsqrtW : Ksqrt ≤ W)
    (hKclog2W : Kclog2 ≤ W)
    (hKpow2W : Kpow2 ≤ W)
    (hKdup : Kdup ≤ W)
    (hKdrop : Kdrop ≤ W)
    (hKswap : Kswap ≤ W)
    (hKpick : Kpick ≤ W)
    (hKroll : Kroll ≤ W)
    (hKpush : Kpush ≤ W)
    (hKadd : Kadd ≤ W)
    (hKsub : Ksub ≤ W)
    (hKneg : Kneg ≤ W)
    (hKlt : Klt ≤ W)
    (hKmulS : KmulS ≤ W)
    (hKfdiv : Kfdiv ≤ W)
    (hKsqrt : Ksqrt ≤ W)
    (hKclog2 : Kclog2 ≤ W)
    (hKpow2 : Kpow2 ≤ W)
    (hW77 : 77 ≤ W)
    (hKifZero : KifZero ≤ W)
    (hKmapList : KmapList ≤ W)
    (hSB20 : W ^ 20 ≤ SB)
    (hSB30 : W ^ 20 ≤ W ^ 30)
    (hSB34 : W ^ 34 ≤ W ^ 34)
    (hSB37 : W ^ 37 ≤ SB)
    (hbparT : (bpar n).size ≤ n.size + 4)
    (hpparT : (ppar n).size ≤ n.size + 4)
    (haparT : (apar n).size ≤ n.size + 4)
    (hkTparT : (kTpar n).size ≤ n.size + 4)
    (hTparT : (Tpar n).size ≤ n.size + 4)
    (hkrparT : (krpar n).size ≤ n.size + 4)
    (hrparT : (rpar n).size ≤ n.size + 4)
    (hdparT : (dpar n).size ≤ n.size + 4)
    (hLparT : (Lpar n).size ≤ n.size + 4)
    (huparT : (upar n).size ≤ n.size + 4)
    (hNsz : n.size ≤ n.size + 50)
    (hbpar : (bpar n).size ≤ n.size + 50)
    (hppar : (ppar n).size ≤ n.size + 50)
    (hapar : (apar n).size ≤ n.size + 50)
    (hkTpar : (kTpar n).size ≤ n.size + 50)
    (hTpar : (Tpar n).size ≤ n.size + 50)
    (hkrpar : (krpar n).size ≤ n.size + 50)
    (hrpar : (rpar n).size ≤ n.size + 50)
    (hdpar : (dpar n).size ≤ n.size + 50)
    (hLpar : (Lpar n).size ≤ n.size + 50)
    (hupar : (upar n).size ≤ n.size + 50)
    (hupar4 : (upar n).size ≤ n.size + 4)
    (h6c : (6:ℕ).size ≤ n.size + 50)
    (h1 : (1:ℕ).size ≤ n.size + 50)
    (h2c : (2:ℕ).size ≤ n.size + 50)
    (h4c : (4:ℕ).size ≤ n.size + 50)
    (hD : (D:ℕ).size ≤ n.size + 50)
    (hDv : (D:ℕ).size ≤ 11)
    (hDm1 : (D - 1).size ≤ n.size + 50)
    (h2Dm1v : (2 * D - 1).size ≤ 13)
    (h2Dm1 : (2 * D - 1).size ≤ n.size + 50)
    (h4Dv : (4 * D).size ≤ 14)
    (h4D : (4 * D).size ≤ n.size + 50)
    (hFfacT : (Ffac).size ≤ n.size + 4)
    (hQallT : (Qall).size ≤ n.size + 4)
    (hFfac : (Ffac).size ≤ n.size + 50)
    (hFfac4 : (Ffac).size ≤ n.size + 4)
    (hQall : (Qall).size ≤ n.size + 50)
    (hFQ3 : (Ffac * Qall).size ≤ n.size + 4)
    (hFQ : (Ffac * Qall).size ≤ n.size + 50)
    (hK13 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hK1 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (h2Fv : (2 * Ffac).size ≤ n.size + 4)
    (h2F : (2 * Ffac).size ≤ n.size + 50)
    (h2F4 : (2 * Ffac).size ≤ n.size + 4)
    (hDD : (12 * D * D).size ≤ 26)
    (hDDbT : (12 * D * D * bpar n).size ≤ n.size + 30)
    (hDDb : (12 * D * D * bpar n).size ≤ n.size + 50)
    (hDDb1 : (12 * D * D * bpar n - 1).size ≤ n.size + 50)
    (hSQ1 : (Nat.sqrt (12 * D * D * bpar n - 1)).size ≤ n.size + 50)
    (hSQ2 : (Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1))).size ≤ n.size + 50)
    (hN4T : (4 * n).size ≤ n.size + 3)
    (hN4 : (4 * n).size ≤ n.size + 50)
    (hN4bT : (4 * n + bpar n).size ≤ n.size + 5)
    (hN4b : (4 * n + bpar n).size ≤ n.size + 50)
    (hN4b1 : (4 * n + bpar n - 1).size ≤ n.size + 50)
    (hQVT : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 5)
    (hQV : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 50)
    (hDKRT : (D * krpar n).size ≤ n.size + 20)
    (hDKR : (D * krpar n).size ≤ n.size + 50)
    (hR2D1T : (rpar n * (2 * D - 1)).size ≤ n.size + 20)
    (hR2D1 : (rpar n * (2 * D - 1)).size ≤ n.size + 50)
    (hR4D : (rpar n * (2 * D - 1) / (4 * D)).size ≤ n.size + 50)
    (hLK1T : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 5)
    (hLK1 : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 50)
    (hMMT : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 5)
    (hMM : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 50)
    (hMFQ : (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall)).size ≤ n.size + 50)
    (hVLD : vsz (HvdH.intList (List.range D)) ≤ V)
    (hVss : vsz (HvdH.intList (ssPar n)) ≤ V)
    (hVts : vsz (HvdH.intList (tsPar n)) ≤ V)
    (hVLD2 : vsz (intList2 (List.range D)) ≤ V)
    (hVssl : vsz (intList2 (ssPar n)) ≤ V)
    (hVtsl : vsz (intList2 (tsPar n)) ≤ V)
    (hDleW : D ≤ W)
    (hbparposN : 0 < bpar n)
    (hkTw : kTpar n ≤ W)
    (hkrw : krpar n ≤ W)
    (hLpos : 0 < Lpar n)
    (huparpos : 0 < upar n)
    (hposDDb : 0 < 12 * D * D * bpar n)
    (hposN4b : 0 < 4 * n + bpar n)
    (hneg1isz : isz (-1 : ℤ) ≤ W)
    (Hbparpos : (0:ℤ) < (bpar n : ℤ))
    (Hdpos : (0:ℤ) < (D : ℤ))
    (H4Dpos : (0:ℤ) < (4 * D : ℤ))
    (HFQpos : (0:ℤ) < (Ffac * Qall : ℤ))
    (hDle : HvdH.D ≤ 2 ^ 11)
    (hVs26 : (26:ℕ) + 2 ≤ V)
    (hVs51 : n.size + 50 + 1 + 2 ≤ V)
    (hVs11 : (11:ℕ) + 2 ≤ V)
    (hVs12 : (12:ℕ) + 2 ≤ V)
    (hVs24 : ((n.size + 4) + 2) + 2 ≤ V)
    (hVsFk : ((n.size + 4) + 12) + 2 ≤ V)
    (hVsUk : (((n.size + 4) + 12) + 1) + 2 ≤ V)
    (hVs50 : n.size + 50 + 2 ≤ V)
    (hVWle : V ≤ W)
    (hWs26 : (26:ℕ) + 2 ≤ W)
    (hWs51 : n.size + 50 + 1 + 2 ≤ W)
    (hWs11 : (11:ℕ) + 2 ≤ W)
    (hWs12 : (12:ℕ) + 2 ≤ W)
    (hWs24 : ((n.size + 4) + 2) + 2 ≤ W)
    (hWsFk : ((n.size + 4) + 12) + 2 ≤ W)
    (hWsUk : (((n.size + 4) + 12) + 1) + 2 ≤ W)
    (hWs50 : n.size + 50 + 2 ≤ W)
    (hc6 : Nat.size 6 ≤ n.size + 4)
    (hcDD : (12 * D * D).size ≤ n.size + 4)
    (hc1 : Nat.size 1 ≤ n.size + 4)
    (hc4 : Nat.size 4 ≤ n.size + 4)
    (hcDm1 : (D - 1).size ≤ n.size + 4)
    (hcDz : D.size ≤ n.size + 4)
    (hc2Dm1 : (2 * D - 1).size ≤ n.size + 4)
    (hc4D : (4 * D).size ≤ n.size + 4)
    (hcF : Ffac.size ≤ n.size + 4)
    (hcQ : Qall.size ≤ n.size + 4)
    (hcFQ : (Ffac * Qall).size ≤ n.size + 4)
    (hcK1z : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4)
    (hc2F : (2 * Ffac).size ≤ n.size + 4)
    :
    WordR main (Cmd.seq (Cmd.seq (Cmd.seq ((rollP 2)) (dropP)) (Cmd.seq ((rollP 2)) (dropP))) (Cmd.seq (Cmd.seq ((rollP 2)) ((rollP 3))) (Cmd.seq ((rollP 4)) (Cmd.seq ((rollP 5)) ((rollP 6)))))) (fun vs => vs = intList2 (tsPar n) :: intList2 (ssPar n) :: .int ((upar n : ℕ) : ℤ) :: .int ((dpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((bpar n : ℕ) : ℤ) :: R) (fun _ out => out = .int ((bpar n : ℕ) : ℤ) :: .int ((ppar n : ℕ) : ℤ) :: .int ((apar n : ℕ) : ℤ) :: .int ((Tpar n : ℕ) : ℤ) :: .int ((rpar n : ℕ) : ℤ) :: intList2 (tsPar n) :: intList2 (ssPar n) :: R) (fun _ => 9 * SB) := by
  let v1 : Val := .int ((bpar n : ℕ) : ℤ)
  let v2 : Val := .int ((ppar n : ℕ) : ℤ)
  let v3 : Val := .int ((12 * D * D : ℕ) : ℤ)
  let v4 : Val := .int ((12 * D * D * bpar n : ℕ) : ℤ)
  let v5 : Val := .int ((12 * D * D * bpar n - 1 : ℕ) : ℤ)
  let v6 : Val := .int ((Nat.sqrt (12 * D * D * bpar n - 1) : ℕ) : ℤ)
  let v7 : Val := .int ((Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1)) : ℕ) : ℤ)
  let v8 : Val := .int ((apar n : ℕ) : ℤ)
  let v9 : Val := .int ((4 * n : ℕ) : ℤ)
  let v10 : Val := .int ((4 * n + bpar n : ℕ) : ℤ)
  let v11 : Val := .int ((4 * n + bpar n - 1 : ℕ) : ℤ)
  let v12 : Val := .int (((4 * n + bpar n - 1) / bpar n : ℕ) : ℤ)
  let v13 : Val := .int ((kTpar n : ℕ) : ℤ)
  let v14 : Val := .int ((Tpar n : ℕ) : ℤ)
  let v15 : Val := .int ((D - 1 : ℕ) : ℤ)
  let v16 : Val := .int ((kTpar n + (D - 1) : ℕ) : ℤ)
  let v17 : Val := .int ((krpar n : ℕ) : ℤ)
  let v18 : Val := .int ((rpar n : ℕ) : ℤ)
  let v19 : Val := .int ((D * krpar n : ℕ) : ℤ)
  let v20 : Val := .int ((dpar n : ℕ) : ℤ)
  let v21 : Val := .int (((2 * D - 1) : ℕ) : ℤ)
  let v22 : Val := .int ((rpar n * (2 * D - 1) : ℕ) : ℤ)
  let v23 : Val := .int (((4 * D) : ℕ) : ℤ)
  let v24 : Val := .int ((rpar n * (2 * D - 1) / (4 * D) : ℕ) : ℤ)
  let v25 : Val := .int ((Lpar n : ℕ) : ℤ)
  let v26 : Val := .int ((Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v27 : Val := .int ((Lpar n + Ffac * Qall - 1 - Qall : ℕ) : ℤ)
  let v28 : Val := .int ((Ffac * Qall : ℕ) : ℤ)
  let v29 : Val := .int (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall) : ℕ) : ℤ)
  let v30 : Val := .int ((((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall) : ℕ) : ℤ)
  let v31 : Val := .int ((Qall : ℕ) : ℤ)
  let v32 : Val := .int ((upar n : ℕ) : ℤ)
  have P680 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P681 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P682 : vsz (v32) ≤ V := (vszV (hupar) hVs50)
  have S : vsh 3 (intList2 (tsPar n) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 3 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P680) (Nat.add_le_add (P681) (Nat.add_le_add (P682) (le_refl 0)))) (le_of_eq (by ring))
  have H69 : WordR main _ (fun vs => vs = intList2 (tsPar n) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v32 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (2) (intList2 (tsPar n) :: intList2 (ssPar n) :: v32 :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 2 < 9) (Nat.le_add_left 9 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 3 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 3 ≤ 100) hW100)))
  have H70 : WordR main _ (fun vs => vs = v32 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    dropStep hK (hdrop main) (v32) (intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKdrop (vszV (hupar) hVs50) hVW)
  have P700 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P701 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P702 : vsz (v20) ≤ V := (vszV (hdpar) hVs50)
  have S : vsh 3 (intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 3 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P700) (Nat.add_le_add (P701) (Nat.add_le_add (P702) (le_refl 0)))) (le_of_eq (by ring))
  have H71 : WordR main _ (fun vs => vs = intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v20 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (2) (intList2 (tsPar n) :: intList2 (ssPar n) :: v20 :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 2 < 8) (Nat.le_add_left 8 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 3 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 3 ≤ 100) hW100)))
  have H72 : WordR main _ (fun vs => vs = v20 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    dropStep hK (hdrop main) (v20) (intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (SB) (cost1 hW2 hSB20 hKdrop (vszV (hdpar) hVs50) hVW)
  have P720 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P721 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P722 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have S : vsh 3 (intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) ≤ 3 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P720) (Nat.add_le_add (P721) (Nat.add_le_add (P722) (le_refl 0)))) (le_of_eq (by ring))
  have H73 : WordR main _ (fun vs => vs = intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v14 :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (2) (intList2 (tsPar n) :: intList2 (ssPar n) :: v18 :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 2 < 7) (Nat.le_add_left 7 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 3 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 3 ≤ 100) hW100)))
  have P730 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P731 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P732 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P733 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have S : vsh 4 (v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v14 :: v8 :: v2 :: v1 :: R) ≤ 4 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P730) (Nat.add_le_add (P731) (Nat.add_le_add (P732) (Nat.add_le_add (P733) (le_refl 0))))) (le_of_eq (by ring))
  have H74 : WordR main _ (fun vs => vs = v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v14 :: v8 :: v2 :: v1 :: R) (fun _ out => out = v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v8 :: v2 :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (3) (v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v14 :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 3 < 7) (Nat.le_add_left 7 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 4 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 4 ≤ 100) hW100)))
  have P740 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P741 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P742 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P743 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P744 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have S : vsh 5 (v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v8 :: v2 :: v1 :: R) ≤ 5 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P740) (Nat.add_le_add (P741) (Nat.add_le_add (P742) (Nat.add_le_add (P743) (Nat.add_le_add (P744) (le_refl 0)))))) (le_of_eq (by ring))
  have H75 : WordR main _ (fun vs => vs = v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v8 :: v2 :: v1 :: R) (fun _ out => out = v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v2 :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (4) (v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v8 :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 4 < 7) (Nat.le_add_left 7 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 5 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 5 ≤ 100) hW100)))
  have P750 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have P751 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P752 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P753 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P754 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P755 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have S : vsh 6 (v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v2 :: v1 :: R) ≤ 6 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P750) (Nat.add_le_add (P751) (Nat.add_le_add (P752) (Nat.add_le_add (P753) (Nat.add_le_add (P754) (Nat.add_le_add (P755) (le_refl 0))))))) (le_of_eq (by ring))
  have H76 : WordR main _ (fun vs => vs = v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v2 :: v1 :: R) (fun _ out => out = v2 :: v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v1 :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (5) (v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v2 :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 5 < 7) (Nat.le_add_left 7 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 6 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 6 ≤ 100) hW100)))
  have P760 : vsz (v2) ≤ V := (vszV (hppar) hVs50)
  have P761 : vsz (v8) ≤ V := (vszV (hapar) hVs50)
  have P762 : vsz (v14) ≤ V := (vszV (hTpar) hVs50)
  have P763 : vsz (v18) ≤ V := (vszV (hrpar) hVs50)
  have P764 : vsz (intList2 (tsPar n)) ≤ V := (vsz_intList2_le hVtsl)
  have P765 : vsz (intList2 (ssPar n)) ≤ V := (vsz_intList2_le hVssl)
  have P766 : vsz (v1) ≤ V := (vszV (hbpar) hVs50)
  have S : vsh 7 (v2 :: v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v1 :: R) ≤ 7 * V := by
    rw [vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_cons, vsh_zero]
    exact le_trans (Nat.add_le_add (P760) (Nat.add_le_add (P761) (Nat.add_le_add (P762) (Nat.add_le_add (P763) (Nat.add_le_add (P764) (Nat.add_le_add (P765) (Nat.add_le_add (P766) (le_refl 0)))))))) (le_of_eq (by ring))
  have H77 : WordR main _ (fun vs => vs = v2 :: v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v1 :: R) (fun _ out => out = v1 :: v2 :: v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: R) (fun _ => (SB)) :=
    rollStep hK (hroll main) (6) (v2 :: v8 :: v14 :: v18 :: intList2 (tsPar n) :: intList2 (ssPar n) :: v1 :: R) (Nat.lt_of_lt_of_le (by norm_num : 6 < 7) (Nat.le_add_left 7 R.length)) (SB) (cost3 hW2 hSB20 hKroll (le_trans (by norm_num : 7 ≤ 100) hW100) (pick_sum_le hW4 hVW S (le_trans (by norm_num : 7 ≤ 100) hW100)))
  have CHAIN := seqC hK (seqC hK (seqC hK (H69) (H70)) (seqC hK (H71) (H72))) (seqC hK (seqC hK (H73) (H74)) (seqC hK (H75) (seqC hK (H76) (H77))))
  exact conseqC hK CHAIN ((Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 2 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB)))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_trans (Nat.add_le_add (Nat.le_of_eq (Eq.symm (one_mul SB))) (Nat.le_of_eq (Eq.symm (one_mul SB)))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 1 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 1 2 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 3 SB))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 4 5 SB)))))

/-- Paper 5.1: computing the parameters b, p, alpha, T, r, t_i, s_i from n. -/
theorem params : HvdH.KernelLib → HvdH.IntLib → HvdH.ParamsProp := by
  intro hK hI
  obtain ⟨dupP, Kdup, hdup⟩ := hK.dup
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  obtain ⟨swapP, Kswap, hswap⟩ := hK.swap
  obtain ⟨pickP, Kpick, hpick⟩ := hK.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  obtain ⟨pushP, Kpush, hpush⟩ := hK.pushVal
  obtain ⟨ifZeroP, KifZero, hifZero⟩ := hK.ifZero
  obtain ⟨mapListP, KmapList, hmapList⟩ := hK.mapList
  obtain ⟨addP, Kadd, hadd⟩ := hI.add
  obtain ⟨subP, Ksub, hsub⟩ := hI.sub
  obtain ⟨negP, Kneg, hneg⟩ := hI.neg
  obtain ⟨ltP, Klt, hlt⟩ := hI.lt
  obtain ⟨mulSP, KmulS, hmulS⟩ := hI.mulS
  obtain ⟨fdivP, Kfdiv, hfdiv⟩ := hI.fdiv
  obtain ⟨sqrtP, Ksqrt, hsqrt⟩ := hI.sqrt
  obtain ⟨clog2P, Kclog2, hclog2⟩ := hI.clog2
  obtain ⟨pow2P, Kpow2, hpow2⟩ := hI.pow2
  set Ksum : ℕ := Kdup + Kdrop + Kswap + Kpick + Kroll + Kpush + KifZero + KmapList
    + Kadd + Ksub + Kneg + Klt + KmulS + Kfdiv + Ksqrt + Kclog2 + Kpow2 with hKsumdef
  set K0 : ℕ := Ksum + 2 ^ 44 + 100 with hK0def
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) (clog2P)) (Cmd.seq (dupP) ((pushP (.int ((6 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pickP 1))) (Cmd.seq ((pushP (.int ((12 * D * D : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq ((pushP (.int (-1 : ℤ)))) (addP)) (Cmd.seq (sqrtP) (sqrtP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pickP 3)) ((pushP (.int ((4 : ℕ) : ℤ)))))))) (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (mulSP) ((pickP 3))) (Cmd.seq (addP) ((pushP (.int (-1 : ℤ)))))) (Cmd.seq (Cmd.seq (addP) ((pickP 3))) (Cmd.seq (swapP) (fdivP)))) (Cmd.seq (Cmd.seq (Cmd.seq (clog2P) (dupP)) (Cmd.seq (pow2P) ((pickP 1)))) (Cmd.seq (Cmd.seq ((pushP (.int ((D - 1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((D : ℕ) : ℤ)))) (swapP)))))) (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (fdivP) (dupP)) (Cmd.seq (pow2P) ((pickP 1)))) (Cmd.seq (Cmd.seq ((pushP (.int ((D : ℕ) : ℤ)))) (mulSP)) (Cmd.seq ((pickP 4)) (negP)))) (Cmd.seq (Cmd.seq (Cmd.seq (addP) ((rollP 2))) (Cmd.seq (dropP) ((rollP 3)))) (Cmd.seq (Cmd.seq (dropP) ((rollP 6))) (Cmd.seq (dropP) ((pickP 1)))))) (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq ((pushP (.int (((2 * D - 1) : ℕ) : ℤ)))) (mulSP)) (Cmd.seq ((pushP (.int (((4 * D) : ℕ) : ℤ)))) (swapP))) (Cmd.seq (Cmd.seq (fdivP) ((pushP (.int ((1 : ℕ) : ℤ))))) (Cmd.seq (addP) ((pushP (.int ((Ffac * Qall - 1 - Qall : ℕ) : ℤ))))))) (Cmd.seq (Cmd.seq (Cmd.seq (addP) ((pushP (.int ((Ffac * Qall : ℕ) : ℤ))))) (Cmd.seq (swapP) (fdivP))) (Cmd.seq (Cmd.seq ((pushP (.int ((Ffac * Qall : ℕ) : ℤ)))) (mulSP)) (Cmd.seq ((pushP (.int ((Qall : ℕ) : ℤ)))) (addP))))))) (Cmd.seq ((pushP (intList2 (List.range D)))) ((mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (dupP) ((pickP 3))) (Cmd.seq (swapP) (subP))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (addP)) (Cmd.seq ((pushP (.int ((2 * Ffac : ℕ) : ℤ)))) (mulSP)))) (Cmd.seq (Cmd.seq (Cmd.seq (swapP) (dropP)) (Cmd.seq ((pickP 1)) ((pushP (.int ((2 : ℕ) : ℤ)))))) (Cmd.seq (Cmd.seq (mulSP) ((pushP (.int (-1 : ℤ))))) (Cmd.seq (addP) (addP))))) (Cmd.seq (Cmd.seq ((pushP (.int ((1 : ℕ) : ℤ)))) (Cmd.seq (addP) ((pushP (.int ((Ffac : ℕ) : ℤ)))))) (Cmd.seq (mulSP) (Cmd.seq ((pickP 1)) (addP))))))))))))) (Cmd.seq (Cmd.seq ((pushP (intList2 (List.range D)))) ((mapListP (Cmd.seq (Cmd.seq (dupP) ((pickP 4))) (Cmd.seq (swapP) (Cmd.seq (ltP) ((ifZeroP (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq (Cmd.seq (dropP) ((pickP 3))) (Cmd.seq ((pushP (.int ((2 : ℕ) : ℤ)))) (Cmd.seq (swapP) (fdivP)))))))))))) (Cmd.seq (Cmd.seq (Cmd.seq ((rollP 2)) (dropP)) (Cmd.seq ((rollP 2)) (dropP))) (Cmd.seq (Cmd.seq ((rollP 2)) ((rollP 3))) (Cmd.seq ((rollP 4)) (Cmd.seq ((rollP 5)) ((rollP 6))))))), 65536 * K0, n1, ?_⟩
  intro main n hn
  have hsz : 65755586 ≤ n.size := n1SizeBig n hn
  have hn2 : 1 < n := by
    have h : (2:ℕ) ^ 1 ≤ n := Nat.lt_size.mp (by omega : 1 < n.size)
    omega
  have hK0pos : 1 ≤ K0 := by rw [hK0def]; omega
  have hK0ge : 2 ^ 44 + 100 ≤ K0 := by rw [hK0def]; omega
  set B : ℕ := n.size + 1 with hBdef
  have hB2 : 2 ≤ B := by rw [hBdef]; omega
  set V : ℕ := (KBsz + n.size + 6) * (D + 2) with hVdef
  have hVdef2 : V = (KBsz + n.size + 6) * (D + 2) := hVdef
  set W : ℕ := B ^ K0 with hWdef
  have hW2 : 2 ≤ W := by
    rw [hWdef]
    calc (2:ℕ) ≤ B ^ 1 := by rw [pow_one]; exact hB2
      _ ≤ B ^ K0 := Nat.pow_le_pow_right (by omega) hK0pos
  have hW4 : 4 ≤ W := by
    have : (2:ℕ) ^ 2 ≤ W := by
      rw [hWdef]
      calc (2:ℕ) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hB2 2
        _ ≤ B ^ K0 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hW100 : 100 ≤ W := by
    have : (2:ℕ) ^ 7 ≤ W := by
      rw [hWdef]
      calc (2:ℕ) ^ 7 ≤ B ^ 7 := Nat.pow_le_pow_left hB2 7
        _ ≤ B ^ K0 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hVW : V + 1 ≤ W := by
    rw [hVdef, hWdef, hBdef]
    exact V_le_pow n K0 hsz hK0ge
  have hVsz : n.size + 100 ≤ V := by
    rw [hVdef]
    have h1 : n.size + 6 ≤ KBsz + n.size + 6 := by omega
    have h2 : (3:ℕ) ≤ D + 2 := by norm_num [HvdH.D]
    have h3 : (n.size + 6) * 3 ≤ (KBsz + n.size + 6) * (D + 2) := Nat.mul_le_mul h1 h2
    omega
  have hK0W : K0 ≤ W := by
    rw [hWdef]
    calc K0 ≤ 2 ^ K0 := le_of_lt Nat.lt_two_pow_self
      _ ≤ B ^ K0 := Nat.pow_le_pow_left (by omega : 2 ≤ B) K0
  have hKdupW : Kdup ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKdropW : Kdrop ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKswapW : Kswap ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKpickW : Kpick ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKrollW : Kroll ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKpushW : Kpush ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKifZeroW : KifZero ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKmapListW : KmapList ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKaddW : Kadd ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKsubW : Ksub ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKnegW : Kneg ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKltW : Klt ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKmulSW : KmulS ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKfdivW : Kfdiv ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKsqrtW : Ksqrt ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKclog2W : Kclog2 ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKpow2W : Kpow2 ≤ W := le_trans (by rw [hK0def, hKsumdef]; omega) hK0W
  have hKdup : Kdup ≤ W := hKdupW
  have hKdrop : Kdrop ≤ W := hKdropW
  have hKswap : Kswap ≤ W := hKswapW
  have hKpick : Kpick ≤ W := hKpickW
  have hKroll : Kroll ≤ W := hKrollW
  have hKpush : Kpush ≤ W := hKpushW
  have hKadd : Kadd ≤ W := hKaddW
  have hKsub : Ksub ≤ W := hKsubW
  have hKneg : Kneg ≤ W := hKnegW
  have hKlt : Klt ≤ W := hKltW
  have hKmulS : KmulS ≤ W := hKmulSW
  have hKfdiv : Kfdiv ≤ W := hKfdivW
  have hKsqrt : Ksqrt ≤ W := hKsqrtW
  have hKclog2 : Kclog2 ≤ W := hKclog2W
  have hKpow2 : Kpow2 ≤ W := hKpow2W
  have hW77 : 77 ≤ W := le_trans (by norm_num : (77:ℕ) ≤ 100) hW100
  have hKifZero : KifZero ≤ W := hKifZeroW
  have hKmapList : KmapList ≤ W := hKmapListW
  set SB : ℕ := W ^ 40 with hSBdef
  have hSB20 : W ^ 20 ≤ SB := by rw [hSBdef]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hSB30 : W ^ 20 ≤ W ^ 30 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hSB34 : W ^ 34 ≤ W ^ 34 := le_refl _
  have hSB37 : W ^ 37 ≤ SB := by rw [hSBdef]; exact Nat.pow_le_pow_right (by omega) (by norm_num)

  have hpar := parSizesBig n hsz
  have hL3 := listSizesBig n hsz
  have hbparT : (bpar n).size ≤ n.size + 4 := hpar.1
  have hpparT : (ppar n).size ≤ n.size + 4 := hpar.2.1
  have haparT : (apar n).size ≤ n.size + 4 := hpar.2.2.1
  have hkTparT : (kTpar n).size ≤ n.size + 4 := hpar.2.2.2.1
  have hTparT : (Tpar n).size ≤ n.size + 4 := hpar.2.2.2.2.1
  have hkrparT : (krpar n).size ≤ n.size + 4 := hpar.2.2.2.2.2.1
  have hrparT : (rpar n).size ≤ n.size + 4 := hpar.2.2.2.2.2.2.1
  have hdparT : (dpar n).size ≤ n.size + 4 := hpar.2.2.2.2.2.2.2.1
  have hLparT : (Lpar n).size ≤ n.size + 4 := hpar.2.2.2.2.2.2.2.2.1
  have huparT : (upar n).size ≤ n.size + 4 := hpar.2.2.2.2.2.2.2.2.2
  have hNsz : n.size ≤ n.size + 50 := by omega
  have hbpar : (bpar n).size ≤ n.size + 50 := by omega
  have hppar : (ppar n).size ≤ n.size + 50 := by omega
  have hapar : (apar n).size ≤ n.size + 50 := by omega
  have hkTpar : (kTpar n).size ≤ n.size + 50 := by omega
  have hTpar : (Tpar n).size ≤ n.size + 50 := by omega
  have hkrpar : (krpar n).size ≤ n.size + 50 := by omega
  have hrpar : (rpar n).size ≤ n.size + 50 := by omega
  have hdpar : (dpar n).size ≤ n.size + 50 := by omega
  have hLpar : (Lpar n).size ≤ n.size + 50 := by omega
  have hupar : (upar n).size ≤ n.size + 50 := by omega
  have hupar4 : (upar n).size ≤ n.size + 4 := huparT
  have h6c : (6:ℕ).size ≤ n.size + 50 := by
    have h : (6:ℕ).size ≤ 3 := Nat.size_le.mpr (by norm_num); omega
  have h1 : (1:ℕ).size ≤ n.size + 50 := by
    have h : (1:ℕ).size ≤ 1 := Nat.size_le.mpr (by norm_num); omega
  have h2c : (2:ℕ).size ≤ n.size + 50 := by
    have h : (2:ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num); omega
  have h4c : (4:ℕ).size ≤ n.size + 50 := by
    have h : (4:ℕ).size ≤ 3 := Nat.size_le.mpr (by norm_num); omega
  have hD : (D:ℕ).size ≤ n.size + 50 := by
    have h : (D:ℕ).size ≤ 11 := Nat.size_le.mpr (by norm_num [HvdH.D]); omega
  have hDv : (D:ℕ).size ≤ 11 := Nat.size_le.mpr (by norm_num [HvdH.D])
  have hDm1 : (D - 1).size ≤ n.size + 50 := by have h := szSub_le D 1; omega
  have h2Dm1v : (2 * D - 1).size ≤ 13 := by
    have h := szSub_le (2 * D) 1
    have h2 : (2 * D).size ≤ 13 := by
      have hh := size_mul_le 2 D
      have h3 : (2:ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
      omega
    omega
  have h2Dm1 : (2 * D - 1).size ≤ n.size + 50 := by have h := h2Dm1v; omega
  have h4Dv : (4 * D).size ≤ 14 := by
    have hh := size_mul_le 4 D
    have h3 : (4:ℕ).size ≤ 3 := Nat.size_le.mpr (by norm_num)
    omega
  have h4D : (4 * D).size ≤ n.size + 50 := by have h := h4Dv; omega
  have hc := constSizesBig n hsz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc
  obtain ⟨hc6, hcDD, hc1, hc4, hcDm1, hcDz, hc2Dm1, hc4D, hcF, hcQ, hcFQ, hcK1z, hc2F⟩ := hc
  have hFfacT : (Ffac).size ≤ n.size + 4 := hcF
  have hQallT : (Qall).size ≤ n.size + 4 := hcQ
  have hFfac : (Ffac).size ≤ n.size + 50 := by omega
  have hFfac4 : (Ffac).size ≤ n.size + 4 := hcF
  have hQall : (Qall).size ≤ n.size + 50 := by omega
  have hFQ3 : (Ffac * Qall).size ≤ n.size + 4 := hcFQ
  have hFQ : (Ffac * Qall).size ≤ n.size + 50 := by omega
  have hK13 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4 := hcK1z
  have hK1 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 50 := by omega
  have h2Fv : (2 * Ffac).size ≤ n.size + 4 := hc2F
  have h2F : (2 * Ffac).size ≤ n.size + 50 := by omega
  have h2F4 : (2 * Ffac).size ≤ n.size + 4 := hc2F
  have hDD : (12 * D * D).size ≤ 26 := Nat.size_le.mpr (by norm_num [HvdH.D])
  have hDDbT : (12 * D * D * bpar n).size ≤ n.size + 30 := by
    have h := size_mul_le (12 * D * D) (bpar n)
    have h2 := hDD
    have h3 := hbparT
    omega
  have hDDb : (12 * D * D * bpar n).size ≤ n.size + 50 := by omega
  have hDDb1 : (12 * D * D * bpar n - 1).size ≤ n.size + 50 := by
    have h := szSub_le (12 * D * D * bpar n) 1
    have h2 := hDDbT
    omega
  have hSQ1 : (Nat.sqrt (12 * D * D * bpar n - 1)).size ≤ n.size + 50 := by
    have h := sqrt_size_le (12 * D * D * bpar n - 1)
    have h2 := hDDb1
    omega
  have hSQ2 : (Nat.sqrt (Nat.sqrt (12 * D * D * bpar n - 1))).size ≤ n.size + 50 := by
    have h := sqrt_size_le (Nat.sqrt (12 * D * D * bpar n - 1))
    have h2 := hSQ1
    omega
  have hN4T : (4 * n).size ≤ n.size + 3 := by
    have h := size_mul_le 4 n
    have h2 : (4:ℕ).size ≤ 3 := Nat.size_le.mpr (by norm_num)
    omega
  have hN4 : (4 * n).size ≤ n.size + 50 := by omega
  have hN4bT : (4 * n + bpar n).size ≤ n.size + 5 := by
    have h := szAdd_le (4 * n) (bpar n)
    have h2 := hN4T
    have h3 := hbparT
    omega
  have hN4b : (4 * n + bpar n).size ≤ n.size + 50 := by omega
  have hN4b1 : (4 * n + bpar n - 1).size ≤ n.size + 50 := by
    have h := szSub_le (4 * n + bpar n) 1
    have h2 := hN4bT
    omega
  have hQVT : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 5 :=
    le_trans (szDiv_le (4 * n + bpar n - 1) (bpar n)) (le_trans (szSub_le (4 * n + bpar n) 1) hN4bT)
  have hQV : ((4 * n + bpar n - 1) / bpar n).size ≤ n.size + 50 := by omega
  have hDKRT : (D * krpar n).size ≤ n.size + 20 := by
    have h := size_mul_le D (krpar n)
    have h2 := hDv
    have h3 := hkrparT
    omega
  have hDKR : (D * krpar n).size ≤ n.size + 50 := by omega
  have hR2D1T : (rpar n * (2 * D - 1)).size ≤ n.size + 20 := by
    have h := size_mul_le (rpar n) (2 * D - 1)
    have h2 := hrparT
    have h3 := h2Dm1v
    omega
  have hR2D1 : (rpar n * (2 * D - 1)).size ≤ n.size + 50 := by omega
  have hR4D : (rpar n * (2 * D - 1) / (4 * D)).size ≤ n.size + 50 := by
    have h := szDiv_le (rpar n * (2 * D - 1)) (4 * D)
    have h2 := hR2D1T
    omega
  have hLK1T : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 5 := by
    have h := szSub_le (Lpar n + Ffac * Qall - 1) Qall
    have h2 := szSub_le (Lpar n + Ffac * Qall) 1
    have h3 := szAdd_le (Lpar n) (Ffac * Qall)
    have h4 := hLparT
    have h5 := hFQ3
    omega
  have hLK1 : (Lpar n + Ffac * Qall - 1 - Qall).size ≤ n.size + 50 := by omega
  have hMMT : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 5 :=
    le_trans (szDiv_le (Lpar n + Ffac * Qall - 1 - Qall) (Ffac * Qall)) hLK1T
  have hMM : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)).size ≤ n.size + 50 := by omega
  have hMFQ : (((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall)).size ≤ n.size + 50 :=
    le_trans (Nat.size_le_size (Nat.div_mul_le_self (Lpar n + Ffac * Qall - 1 - Qall) (Ffac * Qall)))
      (le_trans hLK1T (by omega))
  have hVLD : vsz (HvdH.intList (List.range D)) ≤ V := by
    have h := hL3.1
    have h2 := hVsz
    show (HvdH.intList (List.range D)).enc.length ≤ V
    omega
  have hVss : vsz (HvdH.intList (ssPar n)) ≤ V := by
    have h := hL3.2.2
    have hstep : (n.size + 6) * (D + 2) ≤ (KBsz + n.size + 6) * (D + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    show (HvdH.intList (ssPar n)).enc.length ≤ V
    rw [hVdef2]
    exact le_trans h hstep
  have hVts : vsz (HvdH.intList (tsPar n)) ≤ V := by
    have h := hL3.2.1
    have hstep : (n.size + 6) * (D + 2) ≤ (KBsz + n.size + 6) * (D + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    show (HvdH.intList (tsPar n)).enc.length ≤ V
    rw [hVdef2]
    exact le_trans h hstep
  have hVLD2 : vsz (intList2 (List.range D)) ≤ V := vsz_intList2_le hVLD
  have hVssl : vsz (intList2 (ssPar n)) ≤ V := vsz_intList2_le hVss
  have hVtsl : vsz (intList2 (tsPar n)) ≤ V := vsz_intList2_le hVts
  have hDleW : D ≤ W := by
    calc D = 1729 := rfl
      _ ≤ 2 ^ 11 := by norm_num
      _ ≤ 2 ^ K0 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ W := by rw [hWdef]; exact Nat.pow_le_pow_left (by omega : 2 ≤ B) K0
  have hbparposN : 0 < bpar n := by rw [bpar]; exact Nat.clog_pos (by norm_num) hn2
  have hkTw : kTpar n ≤ W := by
    have h := kTpar_le_size n
    omega
  have hkrw : krpar n ≤ W := by
    have h := krpar_le_kTpar n
    have h2 := hkTw
    omega
  have hLpos : 0 < Lpar n := by
    rw [Work.Params.Lpar]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_left 1 _)
  have huparpos : 0 < upar n := lt_of_lt_of_le hLpos (uparfacts n).1
  have hposDDb : 0 < 12 * D * D * bpar n := by
    have h1 : 0 < 12 * D * D := by norm_num [HvdH.D]
    exact Nat.mul_pos h1 hbparposN
  have hposN4b : 0 < 4 * n + bpar n := by
    have h1 := hn2
    have h2 := hbparposN
    omega
  have hneg1isz : isz (-1 : ℤ) ≤ W := by
    rw [HvdH.isz]
    norm_num
    omega
  have Hbparpos : (0:ℤ) < (bpar n : ℤ) := by exact_mod_cast hbparposN
  have Hdpos : (0:ℤ) < (D : ℤ) := by norm_num [HvdH.D]
  have H4Dpos : (0:ℤ) < (4 * D : ℤ) := by norm_num [HvdH.D]
  have HFQpos : (0:ℤ) < (Ffac * Qall : ℤ) := by
    have h : 0 < Ffac * Qall := Nat.mul_pos Ffac_pos Qall_pos
    exact_mod_cast h
  have hDle : HvdH.D ≤ 2 ^ 11 := by norm_num [HvdH.D]
  have hVs26 : (26:ℕ) + 2 ≤ V := by omega
  have hVs51 : n.size + 50 + 1 + 2 ≤ V := by omega
  have hVs11 : (11:ℕ) + 2 ≤ V := by omega
  have hVs12 : (12:ℕ) + 2 ≤ V := by omega
  have hVs24 : ((n.size + 4) + 2) + 2 ≤ V := by omega
  have hVsFk : ((n.size + 4) + 12) + 2 ≤ V := by omega
  have hVsUk : (((n.size + 4) + 12) + 1) + 2 ≤ V := by omega
  have hVs50 : n.size + 50 + 2 ≤ V := by omega
  have hVWle : V ≤ W := le_trans (Nat.le_succ V) hVW
  have hWs26 : (26:ℕ) + 2 ≤ W := le_trans hVs26 hVWle
  have hWs51 : n.size + 50 + 1 + 2 ≤ W := le_trans hVs51 hVWle
  have hWs11 : (11:ℕ) + 2 ≤ W := le_trans hVs11 hVWle
  have hWs12 : (12:ℕ) + 2 ≤ W := le_trans hVs12 hVWle
  have hWs24 : ((n.size + 4) + 2) + 2 ≤ W := le_trans hVs24 hVWle
  have hWsFk : ((n.size + 4) + 12) + 2 ≤ W := le_trans hVsFk hVWle
  have hWsUk : (((n.size + 4) + 12) + 1) + 2 ≤ W := le_trans hVsUk hVWle
  have hWs50 : n.size + 50 + 2 ≤ W := le_trans hVs50 hVWle

  intro vs hpre s Rg hs
  obtain ⟨R, rfl⟩ := hpre
  have S1 := seg1 hK hI main n R dupP Kdup hdup dropP Kdrop hdrop swapP Kswap hswap pickP Kpick hpick rollP Kroll hroll pushP Kpush hpush ifZeroP KifZero hifZero mapListP KmapList hmapList addP Kadd hadd subP Ksub hsub negP Kneg hneg ltP Klt hlt mulSP KmulS hmulS fdivP Kfdiv hfdiv sqrtP Ksqrt hsqrt clog2P Kclog2 hclog2 pow2P Kpow2 hpow2 Ksum K0 B W V SB hKsumdef hK0def hBdef hVdef hWdef hSBdef hKdup hKdrop hKswap hKpick hKroll hKpush hKifZero hKmapList hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hsz hn2 hK0pos hK0ge hB2 hVdef2 hW2 hW4 hW100 hVW hVsz hK0W hKdupW hKdropW hKswapW hKpickW hKrollW hKpushW hKifZeroW hKmapListW hKaddW hKsubW hKnegW hKltW hKmulSW hKfdivW hKsqrtW hKclog2W hKpow2W hKdup hKdrop hKswap hKpick hKroll hKpush hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hW77 hKifZero hKmapList hSB20 hSB30 hSB34 hSB37 hbparT hpparT haparT hkTparT hTparT hkrparT hrparT hdparT hLparT huparT hNsz hbpar hppar hapar hkTpar hTpar hkrpar hrpar hdpar hLpar hupar hupar4 h6c h1 h2c h4c hD hDv hDm1 h2Dm1v h2Dm1 h4Dv h4D hFfacT hQallT hFfac hFfac4 hQall hFQ3 hFQ hK13 hK1 h2Fv h2F h2F4 hDD hDDbT hDDb hDDb1 hSQ1 hSQ2 hN4T hN4 hN4bT hN4b hN4b1 hQVT hQV hDKRT hDKR hR2D1T hR2D1 hR4D hLK1T hLK1 hMMT hMM hMFQ hVLD hVss hVts hVLD2 hVssl hVtsl hDleW hbparposN hkTw hkrw hLpos huparpos hposDDb hposN4b hneg1isz Hbparpos Hdpos H4Dpos HFQpos hDle hVs26 hVs51 hVs11 hVs12 hVs24 hVsFk hVsUk hVs50 hVWle hWs26 hWs51 hWs11 hWs12 hWs24 hWsFk hWsUk hWs50 hc6 hcDD hc1 hc4 hcDm1 hcDz hc2Dm1 hc4D hcF hcQ hcFQ hcK1z hc2F
  have S2 := seg2 hK hI main n R dupP Kdup hdup dropP Kdrop hdrop swapP Kswap hswap pickP Kpick hpick rollP Kroll hroll pushP Kpush hpush ifZeroP KifZero hifZero mapListP KmapList hmapList addP Kadd hadd subP Ksub hsub negP Kneg hneg ltP Klt hlt mulSP KmulS hmulS fdivP Kfdiv hfdiv sqrtP Ksqrt hsqrt clog2P Kclog2 hclog2 pow2P Kpow2 hpow2 Ksum K0 B W V SB hKsumdef hK0def hBdef hVdef hWdef hSBdef hKdup hKdrop hKswap hKpick hKroll hKpush hKifZero hKmapList hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hsz hn2 hK0pos hK0ge hB2 hVdef2 hW2 hW4 hW100 hVW hVsz hK0W hKdupW hKdropW hKswapW hKpickW hKrollW hKpushW hKifZeroW hKmapListW hKaddW hKsubW hKnegW hKltW hKmulSW hKfdivW hKsqrtW hKclog2W hKpow2W hKdup hKdrop hKswap hKpick hKroll hKpush hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hW77 hKifZero hKmapList hSB20 hSB30 hSB34 hSB37 hbparT hpparT haparT hkTparT hTparT hkrparT hrparT hdparT hLparT huparT hNsz hbpar hppar hapar hkTpar hTpar hkrpar hrpar hdpar hLpar hupar hupar4 h6c h1 h2c h4c hD hDv hDm1 h2Dm1v h2Dm1 h4Dv h4D hFfacT hQallT hFfac hFfac4 hQall hFQ3 hFQ hK13 hK1 h2Fv h2F h2F4 hDD hDDbT hDDb hDDb1 hSQ1 hSQ2 hN4T hN4 hN4bT hN4b hN4b1 hQVT hQV hDKRT hDKR hR2D1T hR2D1 hR4D hLK1T hLK1 hMMT hMM hMFQ hVLD hVss hVts hVLD2 hVssl hVtsl hDleW hbparposN hkTw hkrw hLpos huparpos hposDDb hposN4b hneg1isz Hbparpos Hdpos H4Dpos HFQpos hDle hVs26 hVs51 hVs11 hVs12 hVs24 hVsFk hVsUk hVs50 hVWle hWs26 hWs51 hWs11 hWs12 hWs24 hWsFk hWsUk hWs50 hc6 hcDD hc1 hc4 hcDm1 hcDz hc2Dm1 hc4D hcF hcQ hcFQ hcK1z hc2F
  have S3 := seg3 hK hI main n R dupP Kdup hdup dropP Kdrop hdrop swapP Kswap hswap pickP Kpick hpick rollP Kroll hroll pushP Kpush hpush ifZeroP KifZero hifZero mapListP KmapList hmapList addP Kadd hadd subP Ksub hsub negP Kneg hneg ltP Klt hlt mulSP KmulS hmulS fdivP Kfdiv hfdiv sqrtP Ksqrt hsqrt clog2P Kclog2 hclog2 pow2P Kpow2 hpow2 Ksum K0 B W V SB hKsumdef hK0def hBdef hVdef hWdef hSBdef hKdup hKdrop hKswap hKpick hKroll hKpush hKifZero hKmapList hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hsz hn2 hK0pos hK0ge hB2 hVdef2 hW2 hW4 hW100 hVW hVsz hK0W hKdupW hKdropW hKswapW hKpickW hKrollW hKpushW hKifZeroW hKmapListW hKaddW hKsubW hKnegW hKltW hKmulSW hKfdivW hKsqrtW hKclog2W hKpow2W hKdup hKdrop hKswap hKpick hKroll hKpush hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hW77 hKifZero hKmapList hSB20 hSB30 hSB34 hSB37 hbparT hpparT haparT hkTparT hTparT hkrparT hrparT hdparT hLparT huparT hNsz hbpar hppar hapar hkTpar hTpar hkrpar hrpar hdpar hLpar hupar hupar4 h6c h1 h2c h4c hD hDv hDm1 h2Dm1v h2Dm1 h4Dv h4D hFfacT hQallT hFfac hFfac4 hQall hFQ3 hFQ hK13 hK1 h2Fv h2F h2F4 hDD hDDbT hDDb hDDb1 hSQ1 hSQ2 hN4T hN4 hN4bT hN4b hN4b1 hQVT hQV hDKRT hDKR hR2D1T hR2D1 hR4D hLK1T hLK1 hMMT hMM hMFQ hVLD hVss hVts hVLD2 hVssl hVtsl hDleW hbparposN hkTw hkrw hLpos huparpos hposDDb hposN4b hneg1isz Hbparpos Hdpos H4Dpos HFQpos hDle hVs26 hVs51 hVs11 hVs12 hVs24 hVsFk hVsUk hVs50 hVWle hWs26 hWs51 hWs11 hWs12 hWs24 hWsFk hWsUk hWs50 hc6 hcDD hc1 hc4 hcDm1 hcDz hc2Dm1 hc4D hcF hcQ hcFQ hcK1z hc2F
  have S4 := seg4 hK hI main n R dupP Kdup hdup dropP Kdrop hdrop swapP Kswap hswap pickP Kpick hpick rollP Kroll hroll pushP Kpush hpush ifZeroP KifZero hifZero mapListP KmapList hmapList addP Kadd hadd subP Ksub hsub negP Kneg hneg ltP Klt hlt mulSP KmulS hmulS fdivP Kfdiv hfdiv sqrtP Ksqrt hsqrt clog2P Kclog2 hclog2 pow2P Kpow2 hpow2 Ksum K0 B W V SB hKsumdef hK0def hBdef hVdef hWdef hSBdef hKdup hKdrop hKswap hKpick hKroll hKpush hKifZero hKmapList hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hsz hn2 hK0pos hK0ge hB2 hVdef2 hW2 hW4 hW100 hVW hVsz hK0W hKdupW hKdropW hKswapW hKpickW hKrollW hKpushW hKifZeroW hKmapListW hKaddW hKsubW hKnegW hKltW hKmulSW hKfdivW hKsqrtW hKclog2W hKpow2W hKdup hKdrop hKswap hKpick hKroll hKpush hKadd hKsub hKneg hKlt hKmulS hKfdiv hKsqrt hKclog2 hKpow2 hW77 hKifZero hKmapList hSB20 hSB30 hSB34 hSB37 hbparT hpparT haparT hkTparT hTparT hkrparT hrparT hdparT hLparT huparT hNsz hbpar hppar hapar hkTpar hTpar hkrpar hrpar hdpar hLpar hupar hupar4 h6c h1 h2c h4c hD hDv hDm1 h2Dm1v h2Dm1 h4Dv h4D hFfacT hQallT hFfac hFfac4 hQall hFQ3 hFQ hK13 hK1 h2Fv h2F h2F4 hDD hDDbT hDDb hDDb1 hSQ1 hSQ2 hN4T hN4 hN4bT hN4b hN4b1 hQVT hQV hDKRT hDKR hR2D1T hR2D1 hR4D hLK1T hLK1 hMMT hMM hMFQ hVLD hVss hVts hVLD2 hVssl hVtsl hDleW hbparposN hkTw hkrw hLpos huparpos hposDDb hposN4b hneg1isz Hbparpos Hdpos H4Dpos HFQpos hDle hVs26 hVs51 hVs11 hVs12 hVs24 hVsFk hVsUk hVs50 hVWle hWs26 hWs51 hWs11 hWs12 hWs24 hWsFk hWsUk hWs50 hc6 hcDD hc1 hc4 hcDm1 hcDz hc2Dm1 hc4D hcF hcQ hcFQ hcK1z hc2F
  have CHAIN := seqC hK (seqC hK (S1) (S2)) (seqC hK (S3) (S4))
  obtain ⟨out, s', m, hpost, heval, hcost, hstk, hoth⟩ := CHAIN (.int (n : ℤ) :: R) rfl s Rg hs
  refine ⟨out, s', m, ?_, heval, ?_, hstk, hoth⟩
  · refine ⟨R, tsPar n, ssPar n, rfl, ParamOK_tsPar_ssPar n hn, ?_⟩
    rw [hpost, ← intList_eq_intList2, ← intList_eq_intList2]
  · refine cost_bound hB2 hWdef hSBdef hK0pos ?_
    exact Nat.le_trans hcost (Nat.le_trans ((Nat.le_trans (Nat.add_le_add ((Nat.le_trans (Nat.add_le_add ((le_refl _)) ((le_refl _))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 64 2 SB))))) ((Nat.le_trans (Nat.add_le_add ((le_refl _)) ((le_refl _))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 2 9 SB)))))) (Nat.le_of_eq (Eq.symm (Nat.add_mul 66 11 SB))))) (Nat.mul_le_mul_right SB (by norm_num : 77 ≤ 78)))

end Work.Params
