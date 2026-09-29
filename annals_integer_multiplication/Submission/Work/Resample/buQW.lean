import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWas

namespace Work.Resample

/-- The uniform slice word `q` of the one-dimensional `B̃` resampling: given the input vector (of
length `t`, in disc) on top of the static table `buTabList p α s t`, it outputs the `s`-vector
computed by `buPhi` (the truncated Neumann series `J̃' = Σ_{j<n} (-1)^j Ẽ^j` applied to the selected
and halved input, then the diagonal scaling `D̃'` and the permutation `P̃_sᵀ`), in cost
`egCostShape K p α t Cm = K(t+1)(√p+1)(α+1)(Cm(Kp)+p+1) + K(t+1)(p+1)²`.

NOTE (for the prover): `KL, IL, LL, FL` are the library hypotheses; do NOT import the global
`Work.Kernel.kernelLib` etc. (still `sorry`ed). `q` uses no `rest`; the table sits below the input
vector, in the 11-entry layout of `buTabList` (the input vector is never modified in place, it is
consumed: the output vector is pushed in its place, above the table). Suggested staging:
(1) select `u` at the indices `egNu` (a `Label and sort` move driven by the key list, or the
window-slide of the table entries); (2) halve all `s` entries; (3) run the `egN-1` Neumann rounds
of `buRound`: per round, `s` outputs each summing `2·egM p α` terms `Wt(ℓ,h)·v(ℓ+h)` — one
`FxLib.mulF` per term (`4` `Cmd.self` calls each), so `n·s·2m ≲ 4sα√p ≤ K(t+1)(√p+1)(α+1)`
`self` calls; (4) accumulate with the signs list and scale by the diagonal weights (`buDsc`), one
`mulF` per entry; (5) permute by `egGam` (`LayoutLib.sortByKey`). Every entry of the output is
`tdiv(Σ, 2^p)` of a sum of products of an `O(p)`-bit table weight with an in-disc entry, hence stays
in disc. -/
theorem buQW (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = HvdH.ofList (u.map HvdH.cfxVal) :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        u.length = t ∧ (∀ z ∈ u, HvdH.inDisc p z))
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
        vs = HvdH.ofList (u.map HvdH.cfxVal) :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        out = HvdH.cvecVal w :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        w.length = s ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧
        (∀ k : Fin s, w.getD k (0, 0) =
          Work.Resample.buPhi (Work.Resample.buWt p α s t) (Work.Resample.buWd p α s t) p α s t
            (by omega) hcop.symm (fun j => u.getD j (0, 0)) k))
      (fun _ => Work.Resample.egCostShape K p α t Cm) := buQWas KL IL LL FL

end Work.Resample
